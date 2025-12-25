#include "z80_boot.h"

jc_error_t jc_z80_romwbw_chainload(const jc_z80_boot_ops *ops,
                                   jc_u32 entry_addr) {
  if (!ops || !ops->jump) {
    return JC_E_DEV_UNSUPPORTED;
  }
  if (entry_addr == 0u) {
    return JC_E_INTERNAL_ASSERT;
  }
  ops->jump(ops->ctx, entry_addr);
  return JC_E_OK;
}
