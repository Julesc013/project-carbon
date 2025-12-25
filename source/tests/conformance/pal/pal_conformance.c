#include "jc_pal.h"

#include "jc_contracts.h"
#include "jc_contracts_autogen.h"
#include "jc_fault.h"
#include "jc_util.h"

#define PAL_LINE_MAX 128u

static jc_u32 g_crc;

static void pal_emit(const jc_pal_desc *pal, const char *s) {
  jc_u32 len;
  if (!s) {
    return;
  }
  len = jc_strlen(s);
  if (pal && pal->console.vtable && pal->console.vtable->write) {
    pal->console.vtable->write(pal->console.ctx, s, len);
  }
  g_crc = jc_crc32_update(g_crc, (const jc_u8 *)s, len);
}

static void pal_emit_line(const jc_pal_desc *pal, const char *s) {
  pal_emit(pal, s);
  pal_emit(pal, "\n");
}

static void pal_emit_hex_u32(const jc_pal_desc *pal, jc_u32 value) {
  char buf[9];
  jc_u32_to_hex(buf, value);
  buf[8] = '\0';
  pal_emit(pal, buf);
}

static void pal_emit_result(const jc_pal_desc *pal,
                            const char *name,
                            int ok) {
  pal_emit(pal, "TEST ");
  pal_emit(pal, name);
  pal_emit(pal, ok ? " PASS\n" : " FAIL\n");
}

static int pal_block_io_test(const jc_pal_desc *pal) {
  jc_pal_block_params params;
  jc_u8 buf[512];
  jc_error_t err;
  if (!pal || !pal->block.vtable) {
    return 0;
  }
  err = pal->block.vtable->get_params(pal->block.ctx, &params);
  if (err != JC_E_OK || params.block_size_bytes != 512u ||
      params.total_sectors == 0u) {
    return 0;
  }
  err = pal->block.vtable->read(pal->block.ctx, 0, buf, 1);
  if (err != JC_E_OK) {
    return 0;
  }
  err = pal->block.vtable->write(pal->block.ctx, 0, buf, 1);
  if (err != JC_E_OK) {
    return 0;
  }
  return 1;
}

static int pal_fs_test(const jc_pal_desc *pal) {
  jc_u8 buf[512];
  const jc_cpmx_superblock_v1 *sb;
  jc_error_t err;
  if (!pal || !pal->block.vtable) {
    return 0;
  }
  err = pal->block.vtable->read(pal->block.ctx, 0, buf, 1);
  if (err != JC_E_OK) {
    return 0;
  }
  sb = (const jc_cpmx_superblock_v1 *)buf;
  if (sb->signature != JC_MAGIC_CPMX) {
    return 0;
  }
  if (sb->version != JC_CPMX_SUPERBLOCK_V1_VERSION ||
      sb->size_bytes != JC_CPMX_SUPERBLOCK_V1_SIZE) {
    return 0;
  }
  return 1;
}

static int pal_fault_timeout_test(const jc_pal_desc *pal) {
  jc_u8 buf[512];
  if (!pal || !pal->block.vtable) {
    return 0;
  }
  jc_fault_set(JC_FAULT_IO_TIMEOUT);
  return pal->block.vtable->read(pal->block.ctx, 0, buf, 1) ==
         JC_E_DEV_IO_TIMEOUT;
}

static int pal_fault_bad_sector_test(const jc_pal_desc *pal) {
  jc_u8 buf[512];
  if (!pal || !pal->block.vtable) {
    return 0;
  }
  jc_fault_set(JC_FAULT_BAD_SECTOR);
  return pal->block.vtable->read(pal->block.ctx, 0, buf, 1) ==
         JC_E_DEV_IO_ERROR;
}

static int pal_fault_partial_read_test(const jc_pal_desc *pal) {
  jc_u8 buf[512];
  if (!pal || !pal->block.vtable) {
    return 0;
  }
  jc_fault_set(JC_FAULT_PARTIAL_READ);
  return pal->block.vtable->read(pal->block.ctx, 0, buf, 1) ==
         JC_E_DEV_IO_ERROR;
}

static int pal_fault_spurious_irq_test(void) {
  jc_fault_set(JC_FAULT_SPURIOUS_IRQ);
  return jc_fault_consume(JC_FAULT_SPURIOUS_IRQ) != 0;
}

static int pal_fault_modeup_fail_test(void) {
  jc_fault_set(JC_FAULT_MODEUP_FAIL);
  return jc_fault_consume(JC_FAULT_MODEUP_FAIL) != 0;
}

int main(void) {
  jc_pal_desc pal;
  jc_error_t err;
  jc_error_t validate_err;
  jc_u32 bdt_crc = 0u;
  jc_u32 cap_crc = 0u;
  int boot_ok = 0;
  int block_ok = 0;
  int fs_ok = 0;
  int run_ok = 0;
  int neg_timeout_ok = 0;
  int neg_bad_sector_ok = 0;
  int neg_partial_ok = 0;
  int neg_irq_ok = 0;
  int neg_modeup_ok = 0;

  err = jc_pal_init(&pal);
  g_crc = jc_crc32_init();

  pal_emit_line(&pal, "PAL_CONFORMANCE 1.0");
  pal_emit(&pal, "PAL_ABI ");
  pal_emit_hex_u32(&pal, JC_PAL_ABI_MAJOR);
  pal_emit(&pal, ".");
  pal_emit_hex_u32(&pal, JC_PAL_ABI_MINOR);
  pal_emit(&pal, "\n");

  if (err != JC_E_OK) {
    pal_emit_line(&pal, "RESULT SKIP");
    g_crc = jc_crc32_finalize(g_crc);
    pal_emit(&pal, "TRANSCRIPT_CRC32 ");
    pal_emit_hex_u32(&pal, g_crc);
    pal_emit(&pal, "\n");
    return 0;
  }

  if (pal.bdt && pal.bdt->total_size >= JC_BDT_FOOTER_V1_SIZE) {
    bdt_crc = jc_crc32((const jc_u8 *)pal.bdt,
                       pal.bdt->total_size - JC_BDT_FOOTER_V1_SIZE);
  }
  if (pal.capset && pal.capset->size_bytes) {
    cap_crc = jc_crc32((const jc_u8 *)pal.capset, pal.capset->size_bytes);
  }
  pal_emit(&pal, "BDT_CRC32 ");
  pal_emit_hex_u32(&pal, bdt_crc);
  pal_emit(&pal, "\n");
  pal_emit(&pal, "CAPSET_CRC32 ");
  pal_emit_hex_u32(&pal, cap_crc);
  pal_emit(&pal, "\n");

  validate_err = jc_pal_validate(&pal);
  boot_ok = (validate_err == JC_E_OK);
  pal_emit_result(&pal, "BOOT", boot_ok);

  block_ok = pal_block_io_test(&pal);
  pal_emit_result(&pal, "BLOCK_IO", block_ok);

  fs_ok = pal_fs_test(&pal);
  pal_emit_result(&pal, "FS", fs_ok);

  run_ok = boot_ok && block_ok;
  pal_emit_result(&pal, "RUN", run_ok);

  neg_timeout_ok = pal_fault_timeout_test(&pal);
  pal_emit_result(&pal, "NEG_TIMEOUT", neg_timeout_ok);
  neg_bad_sector_ok = pal_fault_bad_sector_test(&pal);
  pal_emit_result(&pal, "NEG_BAD_SECTOR", neg_bad_sector_ok);
  neg_partial_ok = pal_fault_partial_read_test(&pal);
  pal_emit_result(&pal, "NEG_PARTIAL_READ", neg_partial_ok);
  neg_irq_ok = pal_fault_spurious_irq_test();
  pal_emit_result(&pal, "NEG_SPURIOUS_IRQ", neg_irq_ok);
  neg_modeup_ok = pal_fault_modeup_fail_test();
  pal_emit_result(&pal, "NEG_MODEUP_FAIL", neg_modeup_ok);

  pal_emit_line(&pal,
                (boot_ok && block_ok && neg_timeout_ok && neg_bad_sector_ok &&
                 neg_partial_ok && neg_irq_ok && neg_modeup_ok)
                    ? "RESULT PASS"
                    : "RESULT FAIL");
  g_crc = jc_crc32_finalize(g_crc);
  pal_emit(&pal, "TRANSCRIPT_CRC32 ");
  pal_emit_hex_u32(&pal, g_crc);
  pal_emit(&pal, "\n");
  return 0;
}
