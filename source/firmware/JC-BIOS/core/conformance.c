#include "jc_conformance.h"

#include "jc_bios.h"
#include "jc_block.h"
#include "jc_console.h"
#include "jc_contracts_autogen.h"
#include "jc_bdt.h"
#include "jc_util.h"
#include "fs_cpmx.h"
#include "loader_jcom.h"
#include "jc_mode.h"
#include "jc_offsets_autogen.h"

typedef struct {
  jc_u32 crc;
} jc_transcript;

static void jc_transcript_begin(jc_transcript *t) {
  t->crc = jc_crc32_init();
}

static void jc_transcript_write_bytes(jc_transcript *t, const char *s) {
  jc_u32 len = jc_strlen(s);
  if (len > 0) {
    t->crc = jc_crc32_update(t->crc, (const jc_u8 *)s, len);
    jc_console_write_raw(s);
  }
}

static void jc_transcript_write_hex32(jc_transcript *t, jc_u32 value) {
  char buf[9];
  jc_u32_to_hex(buf, value);
  buf[8] = '\0';
  jc_transcript_write_bytes(t, buf);
}

static void jc_transcript_write_hex16(jc_transcript *t, jc_u16 value) {
  char buf[5];
  jc_u16_to_hex(buf, value);
  buf[4] = '\0';
  jc_transcript_write_bytes(t, buf);
}

static void jc_transcript_write_lf(jc_transcript *t) {
  const char lf[2] = {'\n', '\0'};
  t->crc = jc_crc32_update(t->crc, (const jc_u8 *)lf, 1);
  jc_console_write_raw(lf);
}

static void jc_transcript_line(jc_transcript *t, const char *line) {
  jc_transcript_write_bytes(t, line);
  jc_transcript_write_lf(t);
}

static void jc_transcript_header(jc_transcript *t) {
  jc_transcript_line(t, "JC_CONFORMANCE 1");
  jc_transcript_line(
      t,
      "CONTRACTS SPEC_TIERS=1.0 SPEC_PROFILES=1.0 SPEC_MODE=1.0 "
      "SPEC_DISCOVERY=1.0 SPEC_CAPSET=1.0 SPEC_TOPOLOGY=1.0 SPEC_BDT=1.0 "
      "SPEC_IRQ=1.0 SPEC_DEV_UART=1.0 SPEC_DEV_TIMER=1.0 SPEC_DEV_PIC=1.0 "
      "SPEC_DEV_STORAGE_IDEPIO=1.0 SPEC_CAI=1.0 SPEC_JCOM=1.0 "
      "SPEC_FS_CPMX=1.0 SPEC_CONFORMANCE=1.0");
  jc_transcript_write_bytes(t, "CAPSET_CRC32 ");
  jc_transcript_write_hex32(t, jc_boot_capset_crc32());
  jc_transcript_write_lf(t);
  jc_transcript_write_bytes(t, "BDT_CRC32 ");
  jc_transcript_write_hex32(t, jc_boot_bdt_crc32());
  jc_transcript_write_lf(t);
}

static void jc_transcript_result(jc_transcript *t, int pass) {
  if (pass) {
    jc_transcript_line(t, "RESULT PASS");
  } else {
    jc_transcript_line(t, "RESULT FAIL");
  }
}

static void jc_transcript_test(jc_transcript *t,
                               const char *id,
                               int pass,
                               jc_u16 err) {
  jc_transcript_write_bytes(t, "TEST ");
  jc_transcript_write_bytes(t, id);
  if (pass) {
    jc_transcript_write_bytes(t, " PASS");
    jc_transcript_write_lf(t);
  } else {
    jc_transcript_write_bytes(t, " FAIL ");
    jc_transcript_write_hex16(t, err);
    jc_transcript_write_lf(t);
  }
}

static void jc_transcript_end(jc_transcript *t) {
  jc_u32 final_crc = jc_crc32_finalize(t->crc);
  jc_console_write_raw("CRC32 ");
  {
    char buf[9];
    jc_u32_to_hex(buf, final_crc);
    buf[8] = '\0';
    jc_console_write_raw(buf);
  }
  jc_console_write_raw("\n");
}

void jc_conformance_v0_1(void) {
  jc_transcript t;
  jc_transcript_begin(&t);
  jc_transcript_header(&t);
  jc_transcript_line(&t, "TEST BOOT PASS");
  jc_transcript_result(&t, 1);
  jc_transcript_end(&t);
}

void jc_conformance_v0_2(void) {
  jc_transcript t;
  jc_transcript_begin(&t);
  jc_transcript_header(&t);
  jc_transcript_line(&t, "TEST MONITOR PASS");
  jc_transcript_result(&t, 1);
  jc_transcript_end(&t);
}

static int g_mode_test_returned = 0;

static void jc_conformance_mode_entry(void) {
  g_mode_test_returned = 1;
  jc_retmd_request();
}

void jc_conformance_v0_3(void) {
  jc_transcript t;
  const jc_capset_v1 *capset = jc_boot_capset();
  jc_u8 start = jc_mode_current_tier();
  jc_u8 max = capset ? capset->presented_cpu_tier : start;
  jc_u8 tier;
  int pass = 1;

  jc_transcript_begin(&t);
  jc_transcript_header(&t);

  for (tier = (jc_u8)(start + 1u); tier <= max; ++tier) {
    jc_mode_abi_v1 capsule;
    jc_error_t err;
    g_mode_test_returned = 0;
    jc_memset(&capsule, 0, sizeof(capsule));
    capsule.version = JC_MODE_ABI_V1_VERSION;
    capsule.size_bytes = JC_STRUCT_MODE_ABI_V1_SIZE;
    capsule.target_tier = tier;
    capsule.entry_vector =
        jc_u64_make((jc_u32)(unsigned long)&jc_conformance_mode_entry, 0);
    err = jc_modeup_request(&capsule);

    jc_transcript_write_bytes(&t, "TEST MODE_P");
    jc_transcript_write_hex16(&t, tier);
    if (err == JC_E_OK && g_mode_test_returned &&
        jc_mode_current_tier() == start) {
      jc_transcript_write_bytes(&t, " PASS");
      jc_transcript_write_lf(&t);
    } else {
      jc_transcript_write_bytes(&t, " FAIL ");
      jc_transcript_write_hex16(&t, err);
      jc_transcript_write_lf(&t);
      pass = 0;
    }
  }

  jc_transcript_result(&t, pass);
  jc_transcript_end(&t);
}

static void jc_conformance_test_bdt_bad_version(jc_transcript *t, int *pass_out) {
  jc_bdt_index idx;
  jc_u8 buf[JC_BDT_HEADER_V1_SIZE + JC_BDT_FOOTER_V1_SIZE];
  jc_bdt_header_v1 *hdr = (jc_bdt_header_v1 *)buf;
  jc_bdt_footer_v1 *ftr = (jc_bdt_footer_v1 *)(buf + JC_BDT_HEADER_V1_SIZE);
  jc_error_t err;

  jc_memset(buf, 0, sizeof(buf));
  hdr->signature = JC_MAGIC_BDT;
  hdr->header_version = 0;
  hdr->header_size = JC_BDT_HEADER_V1_SIZE;
  hdr->entry_size = JC_BDT_ENTRY_V1_SIZE;
  hdr->entry_count = 0;
  hdr->total_size = JC_BDT_HEADER_V1_SIZE + JC_BDT_FOOTER_V1_SIZE;
  ftr->crc32 = jc_crc32(buf, JC_BDT_HEADER_V1_SIZE);

  err = jc_bdt_init(&idx, jc_u64_make((jc_u32)(unsigned long)buf, 0));
  jc_boot_set_phase(JC_BOOT_PHASE_BDT);
  jc_boot_set_error(err);
  if (err == JC_E_BDT_BAD_VERSION &&
      jc_boot_get_phase() == JC_BOOT_PHASE_BDT &&
      jc_boot_get_error() == err) {
    jc_transcript_test(t, "BDT_BAD_VERSION", 1, 0);
  } else {
    jc_transcript_test(t, "BDT_BAD_VERSION", 0, err);
    *pass_out = 0;
  }
}

static void jc_conformance_test_bdt_bad_crc(jc_transcript *t, int *pass_out) {
  jc_bdt_index idx;
  jc_u8 buf[JC_BDT_HEADER_V1_SIZE + JC_BDT_FOOTER_V1_SIZE];
  jc_bdt_header_v1 *hdr = (jc_bdt_header_v1 *)buf;
  jc_bdt_footer_v1 *ftr = (jc_bdt_footer_v1 *)(buf + JC_BDT_HEADER_V1_SIZE);
  jc_error_t err;

  jc_memset(buf, 0, sizeof(buf));
  hdr->signature = JC_MAGIC_BDT;
  hdr->header_version = JC_BDT_HEADER_V1_VERSION;
  hdr->header_size = JC_BDT_HEADER_V1_SIZE;
  hdr->entry_size = JC_BDT_ENTRY_V1_SIZE;
  hdr->entry_count = 0;
  hdr->total_size = JC_BDT_HEADER_V1_SIZE + JC_BDT_FOOTER_V1_SIZE;
  ftr->crc32 = 0;

  err = jc_bdt_init(&idx, jc_u64_make((jc_u32)(unsigned long)buf, 0));
  jc_boot_set_phase(JC_BOOT_PHASE_BDT);
  jc_boot_set_error(err);
  if (err == JC_E_BDT_BAD_CHECKSUM &&
      jc_boot_get_phase() == JC_BOOT_PHASE_BDT &&
      jc_boot_get_error() == err) {
    jc_transcript_test(t, "BDT_BAD_CRC", 1, 0);
  } else {
    jc_transcript_test(t, "BDT_BAD_CRC", 0, err);
    *pass_out = 0;
  }
}

static void jc_conformance_test_storage_blocksize(jc_transcript *t,
                                                  int *pass_out) {
  jc_bdt_entry_v1 entry;
  jc_error_t err;
  jc_memset(&entry, 0, sizeof(entry));
  entry.class_id = JC_DEVCLASS_STORAGE;
  entry.caps0 = JC_DEV_COMPAT_PORT_IO_MASK;
  entry.caps1 = 1;
  entry.io_port_base = 0x1F0u;
  entry.io_port_size = 8;
  entry.block_sector_size = 1024;

  err = jc_storage_validate_entry(&entry);
  if (err == JC_E_DEV_UNSUPPORTED) {
    jc_transcript_test(t, "STORAGE_BLOCKSZ", 1, 0);
  } else {
    jc_transcript_test(t, "STORAGE_BLOCKSZ", 0, err);
    *pass_out = 0;
  }
}

static void jc_conformance_test_storage_timeout(jc_transcript *t,
                                                int *pass_out) {
  jc_error_t err = jc_blk_test_timeout(1);
  if (err == JC_E_DEV_IO_TIMEOUT) {
    jc_transcript_test(t, "STORAGE_TIMEOUT", 1, 0);
  } else {
    jc_transcript_test(t, "STORAGE_TIMEOUT", 0, err);
    *pass_out = 0;
  }
}

void jc_conformance_v0_4(void) {
  jc_transcript t;
  int pass = 1;

  jc_transcript_begin(&t);
  jc_transcript_header(&t);

  jc_conformance_test_bdt_bad_version(&t, &pass);
  jc_conformance_test_bdt_bad_crc(&t, &pass);
  jc_conformance_test_storage_blocksize(&t, &pass);
  jc_conformance_test_storage_timeout(&t, &pass);

  jc_transcript_result(&t, pass);
  jc_transcript_end(&t);
}

static void jc_conformance_fs_write_pattern(jc_u8 *buf, jc_u32 len) {
  jc_u32 i;
  for (i = 0; i < len; ++i) {
    buf[i] = (jc_u8)(i & 0xFFu);
  }
}

void jc_conformance_v0_5(void) {
  jc_transcript t;
  int pass = 1;
  jc_fs_handle handle;
  jc_u8 pattern[300];
  jc_u8 readback[300];
  jc_u32 done = 0;
  jc_error_t err;

  jc_transcript_begin(&t);
  jc_transcript_header(&t);

  err = jc_fs_mount();
  if (err == JC_E_OK) {
    jc_transcript_test(&t, "FS_MOUNT", 1, 0);
  } else {
    jc_transcript_test(&t, "FS_MOUNT", 0, err);
    pass = 0;
  }

  jc_conformance_fs_write_pattern(pattern, sizeof(pattern));
  err = jc_fs_open(&handle, "CONFTEST.TMP",
                   JC_FS_MODE_WRITE | JC_FS_MODE_CREATE | JC_FS_MODE_TRUNC);
  if (err == JC_E_OK) {
    err = jc_fs_write(&handle, pattern, sizeof(pattern), &done);
    jc_fs_close(&handle);
    if (err == JC_E_OK && done == sizeof(pattern)) {
      jc_transcript_test(&t, "FS_WRITE", 1, 0);
    } else {
      jc_transcript_test(&t, "FS_WRITE", 0, err);
      pass = 0;
    }
  } else {
    jc_transcript_test(&t, "FS_WRITE", 0, err);
    pass = 0;
  }

  jc_memset(readback, 0, sizeof(readback));
  err = jc_fs_open(&handle, "CONFTEST.TMP", JC_FS_MODE_READ);
  if (err == JC_E_OK) {
    done = 0;
    err = jc_fs_read(&handle, readback, sizeof(readback), &done);
    jc_fs_close(&handle);
    if (err == JC_E_OK && done == sizeof(readback) &&
        jc_memcmp(pattern, readback, sizeof(readback)) == 0) {
      jc_transcript_test(&t, "FS_READ", 1, 0);
    } else {
      jc_transcript_test(&t, "FS_READ", 0, err);
      pass = 0;
    }
  } else {
    jc_transcript_test(&t, "FS_READ", 0, err);
    pass = 0;
  }

  err = jc_fs_rename("CONFTEST.TMP", "CONFTEST.BIN");
  if (err == JC_E_OK) {
    jc_transcript_test(&t, "FS_RENAME", 1, 0);
  } else {
    jc_transcript_test(&t, "FS_RENAME", 0, err);
    pass = 0;
  }

  err = jc_fs_delete("CONFTEST.BIN");
  if (err == JC_E_OK) {
    jc_transcript_test(&t, "FS_DELETE", 1, 0);
  } else {
    jc_transcript_test(&t, "FS_DELETE", 0, err);
    pass = 0;
  }

  jc_transcript_result(&t, pass);
  jc_transcript_end(&t);
}

static jc_error_t jc_conformance_make_jcom(const char *name, jc_u32 load_addr) {
  jc_fs_handle handle;
  jc_jcom_header_v1 header;
  jc_u8 payload[1];
  jc_u32 crc;
  jc_error_t err;
  jc_u32 wrote = 0;

  payload[0] = 0xC9u;
  jc_memset(&header, 0, sizeof(header));
  header.signature = JC_MAGIC_JCOM;
  header.header_version = JC_JCOM_HEADER_V1_VERSION;
  header.header_size = JC_JCOM_HEADER_V1_SIZE;
  header.min_cpu_tier = JC_TIER_Z80_P0;
  header.load_policy = JC_JCOM_LOAD_FIXED;
  header.load_addr = jc_u64_make(load_addr, 0);
  header.entry_offset = 0;
  header.bss_size = 0;
  header.image_size = sizeof(payload);
  header.tlv_size = 0;
  header.crc32 = 0;

  crc = jc_crc32_init();
  crc = jc_crc32_update(crc, (const jc_u8 *)&header, sizeof(header));
  crc = jc_crc32_update(crc, payload, sizeof(payload));
  header.crc32 = jc_crc32_finalize(crc);

  err = jc_fs_open(&handle, name,
                   JC_FS_MODE_WRITE | JC_FS_MODE_CREATE | JC_FS_MODE_TRUNC);
  if (err != JC_E_OK) {
    return err;
  }
  err = jc_fs_write(&handle, (const jc_u8 *)&header, sizeof(header), &wrote);
  if (err != JC_E_OK || wrote != sizeof(header)) {
    jc_fs_close(&handle);
    return JC_E_EXEC_BAD_CRC;
  }
  err = jc_fs_write(&handle, payload, sizeof(payload), &wrote);
  jc_fs_close(&handle);
  if (err != JC_E_OK || wrote != sizeof(payload)) {
    return JC_E_EXEC_BAD_CRC;
  }
  return JC_E_OK;
}

void jc_conformance_v0_6(void) {
  jc_transcript t;
  int pass = 1;
  jc_jcom_image image;
  jc_error_t err;
  jc_u8 rc = 0;

  jc_transcript_begin(&t);
  jc_transcript_header(&t);

  err = jc_conformance_make_jcom("CONFTEST.JCO", 0x0100u);
  if (err != JC_E_OK) {
    jc_transcript_test(&t, "JCOM_BUILD", 0, err);
    pass = 0;
  } else {
    jc_transcript_test(&t, "JCOM_BUILD", 1, 0);
  }

  err = jc_jcom_load("CONFTEST.JCO", &image);
  if (err == JC_E_OK) {
    jc_transcript_test(&t, "JCOM_LOAD", 1, 0);
  } else {
    jc_transcript_test(&t, "JCOM_LOAD", 0, err);
    pass = 0;
  }

  err = jc_jcom_run("CONFTEST.JCO", &rc);
  if (err == JC_E_OK) {
    jc_transcript_test(&t, "JCOM_RUN", 1, 0);
  } else {
    jc_transcript_test(&t, "JCOM_RUN", 0, err);
    pass = 0;
  }

  err = jc_conformance_make_jcom("BADTEST.JCO", 0x0100u);
  if (err == JC_E_OK) {
    jc_fs_handle handle;
    jc_u32 wrote = 0;
    jc_u8 flip = 0xFFu;
    err = jc_fs_open(&handle, "BADTEST.JCO", JC_FS_MODE_WRITE);
    if (err == JC_E_OK) {
      handle.pos = 40;
      err = jc_fs_write(&handle, &flip, 1, &wrote);
      jc_fs_close(&handle);
    }
  }
  err = jc_jcom_load("BADTEST.JCO", &image);
  if (err == JC_E_EXEC_BAD_CRC) {
    jc_transcript_test(&t, "JCOM_BAD_CRC", 1, 0);
  } else {
    jc_transcript_test(&t, "JCOM_BAD_CRC", 0, err);
    pass = 0;
  }

  jc_transcript_result(&t, pass);
  jc_transcript_end(&t);
}
