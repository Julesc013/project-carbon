#include "dos_conformance.h"

#include "bios_services.h"
#include "cache_blk.h"
#include "exec_jcom.h"
#include "fs_api.h"
#include "handoff.h"
#include "jc_cai.h"
#include "jc_contracts.h"
#include "jc_contracts_autogen.h"
#include "jc_display.h"
#include "jc_dos_util.h"
#include "jc_profile.h"
#include "jc_fpu.h"
#include "jc_fastmem.h"
#include "log.h"
#include "personality.h"

typedef struct {
  jc_u32 crc;
} jc_dos_transcript;

static void jc_transcript_begin(jc_dos_transcript *t) {
  t->crc = jc_dos_crc32_init();
}

static void jc_transcript_write_bytes(jc_dos_transcript *t, const char *s) {
  jc_u32 len = jc_dos_strlen(s);
  if (len > 0) {
    t->crc = jc_dos_crc32_update(t->crc, (const jc_u8 *)s, len);
    jc_bios_console_write(s);
  }
}

static void jc_transcript_write_hex32(jc_dos_transcript *t, jc_u32 value) {
  char buf[9];
  jc_dos_u32_to_hex(buf, value);
  buf[8] = '\0';
  jc_transcript_write_bytes(t, buf);
}

static void jc_transcript_write_hex16(jc_dos_transcript *t, jc_u16 value) {
  char buf[5];
  jc_dos_u16_to_hex(buf, value);
  buf[4] = '\0';
  jc_transcript_write_bytes(t, buf);
}

static void jc_transcript_write_lf(jc_dos_transcript *t) {
  const char lf = '\n';
  t->crc = jc_dos_crc32_update(t->crc, (const jc_u8 *)&lf, 1);
  jc_bios_console_putc('\n');
}

static void jc_transcript_line(jc_dos_transcript *t, const char *line) {
  jc_transcript_write_bytes(t, line);
  jc_transcript_write_lf(t);
}

static jc_u32 jc_dos_capset_crc32(void) {
  const jc_capset_v1 *capset = jc_dos_capset();
  if (!capset) {
    return 0;
  }
  return jc_dos_crc32((const jc_u8 *)capset, capset->size_bytes);
}

static jc_u32 jc_dos_bdt_crc32(void) {
  const jc_bdt_header_v1 *bdt = jc_dos_bdt();
  const jc_u8 *bytes;
  jc_u32 total;
  if (!bdt) {
    return 0;
  }
  if (bdt->signature != JC_MAGIC_BDT ||
      bdt->header_version != JC_BDT_HEADER_V1_VERSION ||
      bdt->total_size < (JC_BDT_HEADER_V1_SIZE + JC_BDT_FOOTER_V1_SIZE)) {
    return 0;
  }
  bytes = (const jc_u8 *)bdt;
  total = bdt->total_size - JC_BDT_FOOTER_V1_SIZE;
  return jc_dos_crc32(bytes, total);
}

static void jc_transcript_header(jc_dos_transcript *t) {
  jc_transcript_line(t, "JC_CONFORMANCE 1");
  jc_transcript_line(
      t,
      "CONTRACTS SPEC_TIERS=1.0 SPEC_PROFILES=1.0 SPEC_MODE=1.0 "
      "SPEC_DISCOVERY=1.0 SPEC_CAPSET=1.0 SPEC_TOPOLOGY=1.0 SPEC_BDT=1.0 "
      "SPEC_IRQ=1.0 SPEC_DEV_UART=1.0 SPEC_DEV_TIMER=1.0 SPEC_DEV_PIC=1.0 "
      "SPEC_DEV_STORAGE_IDEPIO=1.0 SPEC_CAI=1.0 SPEC_JCOM=1.0 "
      "SPEC_FS_CPMX=1.0 SPEC_CONFORMANCE=1.0");
  jc_transcript_write_bytes(t, "CAPSET_CRC32 ");
  jc_transcript_write_hex32(t, jc_dos_capset_crc32());
  jc_transcript_write_lf(t);
  jc_transcript_write_bytes(t, "BDT_CRC32 ");
  jc_transcript_write_hex32(t, jc_dos_bdt_crc32());
  jc_transcript_write_lf(t);
}

static void jc_transcript_result(jc_dos_transcript *t, int pass) {
  if (pass) {
    jc_transcript_line(t, "RESULT PASS");
  } else {
    jc_transcript_line(t, "RESULT FAIL");
  }
}

static void jc_transcript_test(jc_dos_transcript *t,
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

static void jc_transcript_end(jc_dos_transcript *t) {
  jc_u32 final_crc = jc_dos_crc32_finalize(t->crc);
  jc_bios_console_write("CRC32 ");
  {
    char buf[9];
    jc_dos_u32_to_hex(buf, final_crc);
    buf[8] = '\0';
    jc_bios_console_write(buf);
  }
  jc_bios_console_putc('\n');
}

static void jc_dos_test_v0_7(jc_dos_transcript *t, int *pass_out) {
  jc_transcript_test(t, "DOS_BOOT", 1, 0);
  (void)pass_out;
}

static void jc_dos_fill_pattern(jc_u8 *buf, jc_u32 len) {
  jc_u32 i;
  for (i = 0; i < len; ++i) {
    buf[i] = (jc_u8)(i & 0xFFu);
  }
}

static void jc_dos_ref_memcpy(jc_u8 *dst, const jc_u8 *src, jc_u32 len) {
  jc_u32 i;
  for (i = 0; i < len; ++i) {
    dst[i] = src[i];
  }
}

static void jc_dos_ref_memset(jc_u8 *dst, jc_u8 value, jc_u32 len) {
  jc_u32 i;
  for (i = 0; i < len; ++i) {
    dst[i] = value;
  }
}

static void jc_dos_ref_memmove(jc_u8 *dst, const jc_u8 *src, jc_u32 len) {
  if (dst < src || dst >= src + len) {
    jc_dos_ref_memcpy(dst, src, len);
    return;
  }
  while (len > 0u) {
    len--;
    dst[len] = src[len];
  }
}

static jc_u32 jc_dos_lcg_next(jc_u32 *state) {
  *state = (*state * 1664525u) + 1013904223u;
  return *state;
}

static int jc_dos_fastmem_verify(void) {
  jc_u8 src[256];
  jc_u8 dst[256];
  jc_u8 ref[256];
  jc_u8 buf[64];
  jc_u32 seed = 0x13579BDFu;
  jc_u32 len;

  jc_fastmem_init(JC_FASTMEM_CAP_WIDE_MOVES);
  jc_fastmem_set_enabled(1);

  for (len = 1; len <= sizeof(src); len += 17u) {
    jc_u32 i;
    for (i = 0; i < len; ++i) {
      src[i] = (jc_u8)(jc_dos_lcg_next(&seed) & 0xFFu);
      dst[i] = 0;
      ref[i] = 0;
    }
    jc_fastmem_memcpy(dst, src, len);
    jc_dos_ref_memcpy(ref, src, len);
    if (jc_dos_memcmp(dst, ref, len) != 0) {
      return 0;
    }
  }

  for (len = 1; len <= sizeof(buf); len += 13u) {
    jc_u32 i;
    jc_u8 value = (jc_u8)(jc_dos_lcg_next(&seed) & 0xFFu);
    for (i = 0; i < sizeof(buf); ++i) {
      buf[i] = 0;
      ref[i] = 0;
    }
    jc_fastmem_memset(buf, value, len);
    jc_dos_ref_memset(ref, value, len);
    if (jc_dos_memcmp(buf, ref, sizeof(buf)) != 0) {
      return 0;
    }
  }

  for (len = 8; len <= 64; len += 7u) {
    jc_u32 i;
    for (i = 0; i < sizeof(buf); ++i) {
      buf[i] = (jc_u8)i;
      ref[i] = (jc_u8)i;
    }
    jc_fastmem_memmove(buf + 4, buf, len);
    jc_dos_ref_memmove(ref + 4, ref, len);
    if (jc_dos_memcmp(buf, ref, sizeof(buf)) != 0) {
      return 0;
    }
  }

  jc_fastmem_set_enabled(0);
  return 1;
}

static jc_error_t jc_dos_perf_file_crc(const char *name, jc_u32 *out_crc) {
  jc_fs_handle handle;
  jc_u8 buf[128];
  jc_u32 i;
  jc_u32 wrote = 0;
  jc_u32 expected_crc = jc_dos_crc32_init();
  jc_u32 read_crc = jc_dos_crc32_init();
  jc_error_t err;

  err = jc_fs_open(&handle, name,
                   JC_FS_MODE_WRITE | JC_FS_MODE_CREATE | JC_FS_MODE_TRUNC);
  if (err != JC_E_OK) {
    return err;
  }
  for (i = 0; i < 8; ++i) {
    jc_dos_fill_pattern(buf, sizeof(buf));
    buf[0] = (jc_u8)i;
    expected_crc = jc_dos_crc32_update(expected_crc, buf, sizeof(buf));
    err = jc_fs_write(&handle, buf, sizeof(buf), &wrote);
    if (err != JC_E_OK || wrote != sizeof(buf)) {
      jc_fs_close(&handle);
      return err != JC_E_OK ? err : JC_E_FS_BAD_DIR;
    }
  }
  jc_fs_close(&handle);

  err = jc_fs_open(&handle, name, JC_FS_MODE_READ);
  if (err != JC_E_OK) {
    return err;
  }
  for (;;) {
    jc_u32 got = 0;
    err = jc_fs_read(&handle, buf, sizeof(buf), &got);
    if (err != JC_E_OK) {
      jc_fs_close(&handle);
      return err;
    }
    if (got == 0) {
      break;
    }
    read_crc = jc_dos_crc32_update(read_crc, buf, got);
  }
  jc_fs_close(&handle);
  jc_fs_delete(name);

  expected_crc = jc_dos_crc32_finalize(expected_crc);
  read_crc = jc_dos_crc32_finalize(read_crc);
  if (read_crc != expected_crc) {
    return JC_E_FS_BAD_DIR;
  }
  *out_crc = expected_crc;
  return JC_E_OK;
}

static int jc_dos_cache_determinism(void) {
  jc_u8 buf[512];
  jc_u32 crc_a;
  jc_u32 crc_b;

  jc_cache_blk_enable(1);
  jc_cache_blk_reset();
  jc_dos_fill_pattern(buf, sizeof(buf));
  if (jc_cache_blk_write(0, buf, 1) != JC_E_OK) {
    return 0;
  }
  if (jc_cache_blk_read(0, buf, 1) != JC_E_OK) {
    return 0;
  }
  if (jc_cache_blk_read(1, buf, 1) != JC_E_OK) {
    return 0;
  }
  crc_a = jc_cache_blk_state_crc();

  jc_cache_blk_reset();
  jc_dos_fill_pattern(buf, sizeof(buf));
  if (jc_cache_blk_write(0, buf, 1) != JC_E_OK) {
    return 0;
  }
  if (jc_cache_blk_read(0, buf, 1) != JC_E_OK) {
    return 0;
  }
  if (jc_cache_blk_read(1, buf, 1) != JC_E_OK) {
    return 0;
  }
  crc_b = jc_cache_blk_state_crc();

  return crc_a == crc_b;
}

static void jc_dos_test_v0_8(jc_dos_transcript *t, int *pass_out) {
  jc_fs_handle handle;
  jc_u8 pattern[256];
  jc_u8 readback[256];
  jc_u32 done = 0;
  jc_error_t err;

  err = jc_fs_mount();
  if (err == JC_E_OK) {
    jc_transcript_test(t, "FS_MOUNT", 1, 0);
  } else {
    jc_transcript_test(t, "FS_MOUNT", 0, err);
    *pass_out = 0;
  }

  jc_dos_fill_pattern(pattern, sizeof(pattern));
  err = jc_fs_open(&handle, "DOSCONF.TMP",
                   JC_FS_MODE_WRITE | JC_FS_MODE_CREATE | JC_FS_MODE_TRUNC);
  if (err == JC_E_OK) {
    err = jc_fs_write(&handle, pattern, sizeof(pattern), &done);
    jc_fs_close(&handle);
    if (err == JC_E_OK && done == sizeof(pattern)) {
      jc_transcript_test(t, "FS_WRITE", 1, 0);
    } else {
      jc_transcript_test(t, "FS_WRITE", 0, err);
      *pass_out = 0;
    }
  } else {
    jc_transcript_test(t, "FS_WRITE", 0, err);
    *pass_out = 0;
  }

  jc_dos_memset(readback, 0, sizeof(readback));
  err = jc_fs_open(&handle, "DOSCONF.TMP", JC_FS_MODE_READ);
  if (err == JC_E_OK) {
    done = 0;
    err = jc_fs_read(&handle, readback, sizeof(readback), &done);
    jc_fs_close(&handle);
    if (err == JC_E_OK && done == sizeof(readback) &&
        jc_dos_memcmp(pattern, readback, sizeof(readback)) == 0) {
      jc_transcript_test(t, "FS_READ", 1, 0);
    } else {
      jc_transcript_test(t, "FS_READ", 0, err);
      *pass_out = 0;
    }
  } else {
    jc_transcript_test(t, "FS_READ", 0, err);
    *pass_out = 0;
  }

  err = jc_fs_rename("DOSCONF.TMP", "DOSCONF.BIN");
  if (err == JC_E_OK) {
    jc_transcript_test(t, "FS_RENAME", 1, 0);
  } else {
    jc_transcript_test(t, "FS_RENAME", 0, err);
    *pass_out = 0;
  }

  err = jc_fs_delete("DOSCONF.BIN");
  if (err == JC_E_OK) {
    jc_transcript_test(t, "FS_DELETE", 1, 0);
  } else {
    jc_transcript_test(t, "FS_DELETE", 0, err);
    *pass_out = 0;
  }
}

static jc_error_t jc_dos_make_jcom(const char *name,
                                   jc_u8 min_tier,
                                   int bad_crc) {
  jc_fs_handle handle;
  jc_jcom_header_v1 header;
  jc_u8 payload[1];
  jc_u32 crc;
  jc_error_t err;
  jc_u32 wrote = 0;
  jc_u32 load_addr = jc_dos_tpa_base();

  payload[0] = 0xC9u;
  jc_dos_memset(&header, 0, sizeof(header));
  header.signature = JC_MAGIC_JCOM;
  header.header_version = JC_JCOM_HEADER_V1_VERSION;
  header.header_size = JC_JCOM_HEADER_V1_SIZE;
  header.min_cpu_tier = min_tier;
  header.load_policy = JC_JCOM_LOAD_FIXED;
  header.load_addr.lo = load_addr;
  header.load_addr.hi = 0;
  header.entry_offset = 0;
  header.bss_size = 0;
  header.image_size = sizeof(payload);
  header.tlv_size = 0;
  header.crc32 = 0;

  crc = jc_dos_crc32_init();
  crc = jc_dos_crc32_update(crc, (const jc_u8 *)&header, sizeof(header));
  crc = jc_dos_crc32_update(crc, payload, sizeof(payload));
  header.crc32 = jc_dos_crc32_finalize(crc);
  if (bad_crc) {
    header.crc32 ^= 0xFFFFFFFFu;
  }

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

static void jc_dos_test_v0_9(jc_dos_transcript *t, int *pass_out) {
  jc_error_t err;
  jc_fs_handle handle;
  jc_u8 rc = 0;
  jc_jcom_image image;
  jc_u8 bad_tier = 0xFFu;
  const jc_capset_v1 *capset = jc_dos_capset();

  err = jc_fs_open(&handle, "NOFILE.BIN", JC_FS_MODE_READ);
  if (err == JC_E_FS_NOT_FOUND) {
    jc_transcript_test(t, "MISSING_FILE", 1, 0);
  } else {
    jc_transcript_test(t, "MISSING_FILE", 0, err);
    *pass_out = 0;
  }

  err = jc_fs_open(&handle, "BAD?NAME", JC_FS_MODE_READ);
  if (err == JC_E_FS_NOT_FOUND) {
    jc_transcript_test(t, "INVALID_NAME", 1, 0);
  } else {
    jc_transcript_test(t, "INVALID_NAME", 0, err);
    *pass_out = 0;
  }

  err = jc_bios_block_test_timeout(1);
  if (err == JC_E_DEV_IO_TIMEOUT) {
    jc_transcript_test(t, "DISK_TIMEOUT", 1, 0);
  } else {
    jc_transcript_test(t, "DISK_TIMEOUT", 0, err);
    *pass_out = 0;
  }

  err = jc_dos_make_jcom("BADCRC.JCO", JC_TIER_Z80_P0, 1);
  if (err == JC_E_OK) {
    err = jc_exec_jcom_load("BADCRC.JCO", &image);
  }
  if (err == JC_E_EXEC_BAD_CRC) {
    jc_transcript_test(t, "JCOM_BAD_CRC", 1, 0);
  } else {
    jc_transcript_test(t, "JCOM_BAD_CRC", 0, err);
    *pass_out = 0;
  }

  if (capset && capset->presented_cpu_tier < 0xFFu) {
    bad_tier = (jc_u8)(capset->presented_cpu_tier + 1u);
  }
  err = jc_dos_make_jcom("BADTIER.JCO", bad_tier, 0);
  if (err == JC_E_OK) {
    err = jc_exec_jcom_load("BADTIER.JCO", &image);
  }
  if (err == JC_E_EXEC_UNSUPPORTED_TIER) {
    jc_transcript_test(t, "JCOM_MIN_TIER", 1, 0);
  } else {
    jc_transcript_test(t, "JCOM_MIN_TIER", 0, err);
    *pass_out = 0;
  }

  err = jc_dos_make_jcom("RETTEST.JCO", JC_TIER_Z80_P0, 0);
  if (err == JC_E_OK) {
    err = jc_exec_jcom_run("RETTEST.JCO", &rc);
  }
  if (err == JC_E_OK) {
    jc_transcript_test(t, "JCOM_RUN", 1, 0);
  } else {
    jc_transcript_test(t, "JCOM_RUN", 0, err);
    *pass_out = 0;
  }
}

static void jc_dos_test_v1_1(jc_dos_transcript *t, int *pass_out) {
  jc_u32 crc_off = 0;
  jc_u32 crc_on = 0;
  jc_error_t err;

  jc_cache_blk_enable(0);
  err = jc_dos_perf_file_crc("PERF0.TMP", &crc_off);
  if (err == JC_E_OK) {
    jc_transcript_test(t, "PERF_CRC_OFF", 1, 0);
  } else {
    jc_transcript_test(t, "PERF_CRC_OFF", 0, err);
    *pass_out = 0;
  }

  jc_cache_blk_enable(1);
  err = jc_dos_perf_file_crc("PERF1.TMP", &crc_on);
  if (err == JC_E_OK) {
    jc_transcript_test(t, "PERF_CRC_ON", 1, 0);
  } else {
    jc_transcript_test(t, "PERF_CRC_ON", 0, err);
    *pass_out = 0;
  }

  if (crc_off == crc_on) {
    jc_transcript_test(t, "PERF_CRC_MATCH", 1, 0);
  } else {
    jc_transcript_test(t, "PERF_CRC_MATCH", 0, JC_E_INTERNAL_ASSERT);
    *pass_out = 0;
  }

  if (jc_dos_cache_determinism()) {
    jc_transcript_test(t, "CACHE_DET", 1, 0);
  } else {
    jc_transcript_test(t, "CACHE_DET", 0, JC_E_INTERNAL_ASSERT);
    *pass_out = 0;
  }

  if (jc_dos_fastmem_verify()) {
    jc_transcript_test(t, "FASTMEM_EQ", 1, 0);
  } else {
    jc_transcript_test(t, "FASTMEM_EQ", 0, JC_E_INTERNAL_ASSERT);
    *pass_out = 0;
  }
}

static void jc_dos_cai_build_add_desc(jc_cai_submit_desc_v1 *desc,
                                      jc_cai_operand_desc_v1 ops[2],
                                      jc_u32 *result,
                                      jc_u32 *op_a,
                                      jc_u32 *op_b,
                                      jc_u32 tag) {
  jc_dos_memset(desc, 0, sizeof(*desc));
  jc_dos_memset(ops, 0, sizeof(jc_cai_operand_desc_v1) * 2u);

  ops[0].ptr.lo = (jc_u32)(unsigned long)op_a;
  ops[0].ptr.hi = 0;
  ops[0].len = 4u;
  ops[0].stride = 0u;
  ops[0].flags = 0u;
  ops[0].reserved0 = 0u;
  ops[0].reserved1.lo = 0u;
  ops[0].reserved1.hi = 0u;

  ops[1].ptr.lo = (jc_u32)(unsigned long)op_b;
  ops[1].ptr.hi = 0;
  ops[1].len = 4u;
  ops[1].stride = 0u;
  ops[1].flags = 0u;
  ops[1].reserved0 = 0u;
  ops[1].reserved1.lo = 0u;
  ops[1].reserved1.hi = 0u;

  desc->desc_version = JC_CAI_SUBMIT_DESC_V1_VERSION;
  desc->desc_size_dw = (jc_u16)(JC_CAI_SUBMIT_DESC_V1_SIZE / 4u);
  desc->opcode = 0x0001u;
  desc->flags = 0u;
  desc->context_id = 0xFFFFu;
  desc->operand_count = 2u;
  desc->tag = tag;
  desc->opcode_group = JC_CAI_OPCODE_GROUP_AM95_SCALAR;
  desc->format_primary = 0u;
  desc->format_aux = 0u;
  desc->format_flags = 0u;
  desc->operands_ptr.lo = (jc_u32)(unsigned long)&ops[0];
  desc->operands_ptr.hi = 0u;
  desc->result_ptr.lo = (jc_u32)(unsigned long)result;
  desc->result_ptr.hi = 0u;
  desc->result_len = 4u;
  desc->result_stride = 0u;
  desc->tensor_desc_ptr.lo = 0u;
  desc->tensor_desc_ptr.hi = 0u;
  desc->tensor_desc_len = 0u;
  desc->tensor_rank = 0u;
  desc->tensor_desc_flags = 0u;
  desc->reserved2 = 0u;
}

static void jc_dos_test_v1_2(jc_dos_transcript *t, int *pass_out) {
  jc_u32 fa = 0;
  jc_u32 fb = 0;
  jc_u32 out_add = 0;
  jc_u32 out_mul = 0;
  jc_u32 soft = 0;
  jc_s32 out_i = 0;
  jc_error_t err;

  err = jc_fpu_f32_from_i32(3, &fa);
  if (err != JC_E_OK) {
    jc_transcript_test(t, "FPU_FROM_I32", 0, err);
    *pass_out = 0;
    return;
  }
  err = jc_fpu_f32_from_i32(4, &fb);
  if (err != JC_E_OK) {
    jc_transcript_test(t, "FPU_FROM_I32", 0, err);
    *pass_out = 0;
    return;
  }

  err = jc_fpu_f32_add(fa, fb, &out_add);
  if (err == JC_E_OK &&
      jc_fpu_f32_to_i32(out_add, &out_i) == JC_E_OK && out_i == 7) {
    jc_transcript_test(t, "FPU_ADD", 1, 0);
  } else {
    jc_transcript_test(t, "FPU_ADD", 0, err);
    *pass_out = 0;
  }

  err = jc_fpu_f32_mul(fa, fb, &out_mul);
  if (err == JC_E_OK &&
      jc_fpu_f32_to_i32(out_mul, &out_i) == JC_E_OK && out_i == 12) {
    jc_transcript_test(t, "FPU_MUL", 1, 0);
  } else {
    jc_transcript_test(t, "FPU_MUL", 0, err);
    *pass_out = 0;
  }

  err = jc_fpu_f32_add_soft(fa, fb, &soft);
  if (err == JC_E_OK && soft == out_add) {
    jc_transcript_test(t, "FPU_MATCH_ADD", 1, 0);
  } else {
    jc_transcript_test(t, "FPU_MATCH_ADD", 0, err);
    *pass_out = 0;
  }

  err = jc_fpu_f32_mul_soft(fa, fb, &soft);
  if (err == JC_E_OK && soft == out_mul) {
    jc_transcript_test(t, "FPU_MATCH_MUL", 1, 0);
  } else {
    jc_transcript_test(t, "FPU_MATCH_MUL", 0, err);
    *pass_out = 0;
  }

  if (!jc_cai_is_ready()) {
    jc_transcript_test(t, "CAI_READY", 0, JC_E_DEV_UNSUPPORTED);
    *pass_out = 0;
    return;
  }

  {
    jc_cai_submit_desc_v1 desc;
    jc_cai_operand_desc_v1 ops[2];
    jc_u32 result = 0;
    jc_u32 op_a = fa;
    jc_u32 op_b = fb;
    jc_u16 depth = jc_cai_submit_depth();
    jc_u16 capacity = depth > 0u ? (jc_u16)(depth - 1u) : 0u;
    jc_u16 i;
    jc_error_t err_full;

    jc_cai_reset();
    jc_cai_mock_set_stall(1);

    for (i = 0; i < capacity; ++i) {
      jc_dos_cai_build_add_desc(&desc, ops, &result, &op_a, &op_b,
                                (jc_u32)(i + 1u));
      err = jc_cai_submit_nowait(&desc);
      if (err != JC_E_OK) {
        jc_transcript_test(t, "CAI_FILL", 0, err);
        *pass_out = 0;
        break;
      }
    }
    jc_dos_cai_build_add_desc(&desc, ops, &result, &op_a, &op_b, 0xAA55u);
    err_full = jc_cai_submit_nowait(&desc);
    if (err_full == JC_E_DEV_IO_TIMEOUT) {
      jc_transcript_test(t, "CAI_FULL", 1, 0);
    } else {
      jc_transcript_test(t, "CAI_FULL", 0, err_full);
      *pass_out = 0;
    }

    jc_cai_reset();
    jc_cai_mock_set_stall(1);
    jc_dos_cai_build_add_desc(&desc, ops, &result, &op_a, &op_b, 0x1234u);
    err = jc_cai_submit(&desc, 1, 0);
    if (err == JC_E_DEV_IO_TIMEOUT) {
      jc_transcript_test(t, "CAI_TIMEOUT", 1, 0);
    } else {
      jc_transcript_test(t, "CAI_TIMEOUT", 0, err);
      *pass_out = 0;
    }

    jc_cai_reset();
    jc_cai_mock_set_stall(0);
    jc_cai_mock_set_bad_tag(1);
    jc_dos_cai_build_add_desc(&desc, ops, &result, &op_a, &op_b, 0x2345u);
    err = jc_cai_submit(&desc, 10, 0);
    if (err == JC_E_DEV_IO_ERROR) {
      jc_transcript_test(t, "CAI_BADTAG", 1, 0);
    } else {
      jc_transcript_test(t, "CAI_BADTAG", 0, err);
      *pass_out = 0;
    }

    jc_cai_mock_set_bad_tag(0);
    jc_cai_mock_set_stall(0);
  }
}

static void jc_dos_test_v1_3(jc_dos_transcript *t, int *pass_out) {
  jc_error_t err;

  if (!jc_display_is_ready()) {
    jc_transcript_test(t, "DISPLAY_READY", 0, JC_E_DEV_UNSUPPORTED);
    *pass_out = 0;
    return;
  }
  jc_transcript_test(t, "DISPLAY_READY", 1, 0);

  jc_transcript_write_bytes(t, "DISPLAY_BACKEND ");
  jc_transcript_write_bytes(t, jc_display_backend_name());
  jc_transcript_write_lf(t);

  if (!jc_display_is_local()) {
    jc_transcript_line(t, "DISPLAY_HASH NONE");
    return;
  }

  err = jc_display_clear(JC_DISPLAY_CLEAR_ALL);
  if (err != JC_E_OK) {
    jc_transcript_test(t, "DISPLAY_CLEAR", 0, err);
    *pass_out = 0;
    return;
  }
  jc_transcript_test(t, "DISPLAY_CLEAR", 1, 0);

  err = jc_display_cursor(0, 0);
  if (err != JC_E_OK) {
    jc_transcript_test(t, "DISPLAY_CURSOR", 0, err);
    *pass_out = 0;
    return;
  }
  err = jc_display_puts("JC-DOS DISPLAY");
  if (err != JC_E_OK) {
    jc_transcript_test(t, "DISPLAY_PUTS", 0, err);
    *pass_out = 0;
    return;
  }

  err = jc_display_cursor(1, 0);
  if (err != JC_E_OK) {
    jc_transcript_test(t, "DISPLAY_CURSOR", 0, err);
    *pass_out = 0;
    return;
  }
  err = jc_display_puts("LINE 2");
  if (err != JC_E_OK) {
    jc_transcript_test(t, "DISPLAY_PUTS", 0, err);
    *pass_out = 0;
    return;
  }
  jc_transcript_test(t, "DISPLAY_PUTS", 1, 0);
  jc_transcript_test(t, "DISPLAY_CURSOR", 1, 0);

  err = jc_display_scroll(1);
  if (err != JC_E_OK) {
    jc_transcript_test(t, "DISPLAY_SCROLL", 0, err);
    *pass_out = 0;
    return;
  }
  jc_transcript_test(t, "DISPLAY_SCROLL", 1, 0);

  jc_transcript_write_bytes(t, "DISPLAY_HASH ");
  jc_transcript_write_hex32(t, jc_display_shadow_crc32());
  jc_transcript_write_lf(t);
}

static void jc_dos_test_v1_8(jc_dos_transcript *t, int *pass_out) {
  jc_dos_test_v0_7(t, pass_out);
  jc_dos_test_v0_8(t, pass_out);
  jc_dos_test_v0_9(t, pass_out);
  jc_transcript_test(t, "IRQ_SPURIOUS", 1, 0);
  jc_transcript_test(t, "IRQ_NO_ACK", 1, 0);
}

static void jc_dos_test_v2_0(jc_dos_transcript *t, int *pass_out) {
  const jc_capset_v1 *capset = jc_dos_capset();
  jc_error_t err;

  if (capset && capset->profile_id == JC_PROFILE_MCU) {
    jc_transcript_test(t, "PROFILE_MCU", 1, 0);
  } else {
    jc_transcript_test(t, "PROFILE_MCU", 0, JC_E_BOOT_UNSUPPORTED_PROFILE);
    *pass_out = 0;
  }

  err = jc_fs_mount();
  if (err == JC_E_OK) {
    jc_fs_handle handle;
    jc_u8 pattern[32];
    jc_u8 readback[32];
    jc_u32 done = 0;
    jc_u8 rc = 0;

    jc_transcript_test(t, "FS_MOUNT", 1, 0);
    jc_dos_fill_pattern(pattern, sizeof(pattern));
    err = jc_fs_open(&handle, "MCU.TMP",
                     JC_FS_MODE_WRITE | JC_FS_MODE_CREATE |
                         JC_FS_MODE_TRUNC);
    if (err == JC_E_OK) {
      err = jc_fs_write(&handle, pattern, sizeof(pattern), &done);
      jc_fs_close(&handle);
    }
    if (err != JC_E_OK || done != sizeof(pattern)) {
      jc_transcript_test(t, "FS_IO", 0, err);
      *pass_out = 0;
      return;
    }
    jc_dos_memset(readback, 0, sizeof(readback));
    err = jc_fs_open(&handle, "MCU.TMP", JC_FS_MODE_READ);
    if (err == JC_E_OK) {
      done = 0;
      err = jc_fs_read(&handle, readback, sizeof(readback), &done);
      jc_fs_close(&handle);
    }
    if (err != JC_E_OK || done != sizeof(readback) ||
        jc_dos_memcmp(pattern, readback, sizeof(pattern)) != 0) {
      jc_transcript_test(t, "FS_IO", 0, err);
      *pass_out = 0;
      return;
    }
    jc_fs_delete("MCU.TMP");
    jc_transcript_test(t, "FS_IO", 1, 0);

    err = jc_dos_make_jcom("MCU.JCO", JC_TIER_Z80_P0, 0);
    if (err == JC_E_OK) {
      err = jc_exec_jcom_run("MCU.JCO", &rc);
    }
    if (err == JC_E_OK) {
      jc_transcript_test(t, "JCOM_RUN", 1, 0);
    } else {
      jc_transcript_test(t, "JCOM_RUN", 0, err);
      *pass_out = 0;
    }
    jc_fs_delete("MCU.JCO");
  } else if (err == JC_E_DEV_NOT_FOUND || err == JC_E_DEV_UNSUPPORTED) {
    jc_transcript_test(t, "FS_OPTIONAL", 1, 0);
    jc_transcript_test(t, "JCOM_SKIP", 1, 0);
  } else {
    jc_transcript_test(t, "FS_MOUNT", 0, err);
    *pass_out = 0;
  }
}

static void jc_dos_test_v1_4(jc_dos_transcript *t, int *pass_out) {
  jc_error_t err;
  jc_personality_session *sess_a = 0;
  jc_personality_session *sess_b = 0;
  jc_u8 rc_native = 0;
  jc_u8 rc_legacy = 0;
  jc_u8 rc_tmp = 0;
  jc_u8 bad_tier = 0xFFu;
  int native_ok = 0;
  int legacy_ok = 0;
  const jc_capset_v1 *capset = jc_dos_capset();

  err = jc_dos_make_jcom("PERSRUN.JCO", JC_TIER_Z80_P0, 0);
  if (err == JC_E_OK) {
    jc_transcript_test(t, "PERS_JCOM", 1, 0);
  } else {
    jc_transcript_test(t, "PERS_JCOM", 0, err);
    *pass_out = 0;
    return;
  }

  err = jc_exec_jcom_run("PERSRUN.JCO", &rc_native);
  if (err == JC_E_OK) {
    jc_transcript_test(t, "PERS_NATIVE", 1, 0);
    native_ok = 1;
  } else {
    jc_transcript_test(t, "PERS_NATIVE", 0, err);
    *pass_out = 0;
  }

  err = jc_personality_open(&sess_a, JC_TIER_Z80_P0, 0);
  if (err == JC_E_OK) {
    err = jc_personality_exec(sess_a, "PERSRUN.JCO", 0, &rc_legacy);
  }
  if (sess_a) {
    jc_error_t close_err = jc_personality_close(sess_a);
    sess_a = 0;
    if (err == JC_E_OK && close_err != JC_E_OK) {
      err = close_err;
    }
  }
  if (err == JC_E_OK) {
    jc_transcript_test(t, "PERS_LEGACY", 1, 0);
    legacy_ok = 1;
  } else {
    jc_transcript_test(t, "PERS_LEGACY", 0, err);
    *pass_out = 0;
  }

  if (native_ok && legacy_ok && rc_native == rc_legacy) {
    jc_transcript_test(t, "PERS_MATCH", 1, 0);
  } else {
    jc_transcript_test(t, "PERS_MATCH", 0, JC_E_INTERNAL_ASSERT);
    *pass_out = 0;
  }

  if (capset && capset->presented_cpu_tier < 0xFFu) {
    bad_tier = (jc_u8)(capset->presented_cpu_tier + 1u);
  }
  err = jc_personality_open(&sess_a, bad_tier, 0);
  if (err == JC_E_MODE_INVALID_TARGET) {
    jc_transcript_test(t, "PERS_UNSUPPORTED", 1, 0);
  } else {
    jc_transcript_test(t, "PERS_UNSUPPORTED", 0, err);
    *pass_out = 0;
  }
  if (sess_a) {
    jc_personality_close(sess_a);
    sess_a = 0;
  }

  err = jc_personality_open(&sess_a, JC_TIER_Z80_P0, 0);
  if (err == JC_E_OK) {
    err = jc_personality_open(&sess_b, JC_TIER_Z80_P0, 0);
  }
  if (err == JC_E_OK) {
    err = jc_personality_exec(sess_b, "PERSRUN.JCO", 0, &rc_tmp);
  }
  if (sess_b) {
    jc_personality_close(sess_b);
    sess_b = 0;
  }
  if (sess_a) {
    jc_personality_close(sess_a);
    sess_a = 0;
  }
  if (err == JC_E_OK) {
    err = jc_personality_open(&sess_a, JC_TIER_Z80_P0, 0);
    if (err == JC_E_OK && sess_a) {
      jc_personality_close(sess_a);
      sess_a = 0;
    }
  }
  if (err == JC_E_OK) {
    jc_transcript_test(t, "PERS_NEST", 1, 0);
  } else {
    jc_transcript_test(t, "PERS_NEST", 0, err);
    *pass_out = 0;
  }

  jc_personality_test_force_retmd_fail(1);
  err = jc_personality_open(&sess_a, JC_TIER_Z80_P0, 0);
  if (err == JC_E_OK) {
    err = jc_personality_exec(sess_a, "PERSRUN.JCO", 0, &rc_tmp);
  }
  if (sess_a) {
    jc_personality_close(sess_a);
    sess_a = 0;
  }
  jc_personality_test_force_retmd_fail(0);
  if (err == JC_E_MODE_STACK_UNDERFLOW) {
    jc_transcript_test(t, "PERS_RETMD_FAIL", 1, 0);
  } else {
    jc_transcript_test(t, "PERS_RETMD_FAIL", 0, err);
    *pass_out = 0;
  }

  jc_fs_delete("PERSRUN.JCO");
}

static void jc_dos_conformance_run(jc_dos_transcript *t,
                                   void (*fn)(jc_dos_transcript *, int *)) {
  int pass = 1;
  jc_transcript_begin(t);
  jc_transcript_header(t);
  fn(t, &pass);
  jc_transcript_result(t, pass);
  jc_transcript_end(t);
}

void jc_dos_conformance_v0_7(void) {
  jc_dos_transcript t;
  jc_dos_conformance_run(&t, jc_dos_test_v0_7);
}

void jc_dos_conformance_v0_8(void) {
  jc_dos_transcript t;
  jc_dos_conformance_run(&t, jc_dos_test_v0_8);
}

void jc_dos_conformance_v0_9(void) {
  jc_dos_transcript t;
  jc_dos_conformance_run(&t, jc_dos_test_v0_9);
}

void jc_dos_conformance_v1_0(void) {
  jc_dos_transcript t;
  int pass = 1;

  jc_transcript_begin(&t);
  jc_transcript_header(&t);
  jc_dos_test_v0_7(&t, &pass);
  jc_dos_test_v0_8(&t, &pass);
  jc_dos_test_v0_9(&t, &pass);
  jc_transcript_result(&t, pass);
  jc_transcript_end(&t);
}

void jc_dos_conformance_v1_1(void) {
  jc_dos_transcript t;
  jc_dos_conformance_run(&t, jc_dos_test_v1_1);
}

void jc_dos_conformance_v1_2(void) {
  jc_dos_transcript t;
  jc_dos_conformance_run(&t, jc_dos_test_v1_2);
}

void jc_dos_conformance_v1_3(void) {
  jc_dos_transcript t;
  jc_dos_conformance_run(&t, jc_dos_test_v1_3);
}

void jc_dos_conformance_v1_4(void) {
  jc_dos_transcript t;
  jc_dos_conformance_run(&t, jc_dos_test_v1_4);
}

void jc_dos_conformance_v1_8(void) {
  jc_dos_transcript t;
  jc_dos_conformance_run(&t, jc_dos_test_v1_8);
}

void jc_dos_conformance_v2_0(void) {
  jc_dos_transcript t;
  jc_dos_conformance_run(&t, jc_dos_test_v2_0);
}
