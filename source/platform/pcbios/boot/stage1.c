#include "pcbios_boot.h"

jc_error_t jc_pcbios_stage1_load(const jc_pcbios_boot_ops *ops,
                                 jc_u32 lba_start,
                                 jc_u16 sectors,
                                 jc_u32 load_addr) {
  jc_u8 *dst;
  if (!ops || !ops->read_sectors) {
    return JC_E_DEV_UNSUPPORTED;
  }
  if (sectors == 0u || load_addr == 0u) {
    return JC_E_INTERNAL_ASSERT;
  }
  dst = (jc_u8 *)(unsigned long)load_addr;
  return ops->read_sectors(ops->ctx, lba_start, dst, sectors);
}
