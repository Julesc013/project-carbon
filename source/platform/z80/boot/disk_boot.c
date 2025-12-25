#include "z80_boot.h"

jc_error_t jc_z80_disk_boot(const jc_z80_boot_ops *ops,
                            jc_u32 load_addr,
                            jc_u16 sectors) {
  jc_u8 *dst;
  if (!ops || !ops->block_read) {
    return JC_E_DEV_UNSUPPORTED;
  }
  if (load_addr == 0u || sectors == 0u) {
    return JC_E_INTERNAL_ASSERT;
  }
  dst = (jc_u8 *)(unsigned long)load_addr;
  return ops->block_read(ops->ctx, 0, dst, sectors);
}
