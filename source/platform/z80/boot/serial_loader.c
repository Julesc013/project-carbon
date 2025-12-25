#include "z80_boot.h"

static jc_error_t z80_read_byte(const jc_z80_boot_ops *ops, jc_u8 *out) {
  if (!ops || !ops->serial_read || !out) {
    return JC_E_DEV_UNSUPPORTED;
  }
  return ops->serial_read(ops->ctx, out);
}

jc_error_t jc_z80_serial_loader(const jc_z80_boot_ops *ops,
                                jc_u32 load_addr,
                                jc_u32 max_bytes) {
  jc_u8 len_lo;
  jc_u8 len_hi;
  jc_u32 i;
  jc_u32 length;
  jc_u8 *dst;

  if (!ops || !ops->serial_read) {
    return JC_E_DEV_UNSUPPORTED;
  }
  if (load_addr == 0u || max_bytes == 0u) {
    return JC_E_INTERNAL_ASSERT;
  }

  if (z80_read_byte(ops, &len_lo) != JC_E_OK ||
      z80_read_byte(ops, &len_hi) != JC_E_OK) {
    return JC_E_DEV_IO_ERROR;
  }
  length = ((jc_u32)len_hi << 8) | (jc_u32)len_lo;
  if (length > max_bytes) {
    return JC_E_DEV_IO_ERROR;
  }

  dst = (jc_u8 *)(unsigned long)load_addr;
  for (i = 0; i < length; ++i) {
    if (z80_read_byte(ops, &dst[i]) != JC_E_OK) {
      return JC_E_DEV_IO_ERROR;
    }
  }
  return JC_E_OK;
}
