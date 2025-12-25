#include "jc_carbonkio.h"

#define JC_PIC_IRQ_PENDING_OFF 0x0074u

static jc_u32 jc_mmio_read32(jc_u32 base, jc_u32 off) {
  volatile jc_u32 *reg = (volatile jc_u32 *)(unsigned long)(base + off);
  return *reg;
}

jc_error_t jc_carbonkio_pic_init(jc_carbonkio_pic *pic,
                                 const jc_bdt_entry_v1 *entry) {
  if (!pic || !entry) {
    return JC_E_INTERNAL_ASSERT;
  }
  if (entry->mmio_base.hi != 0u || entry->mmio_base.lo == 0u) {
    return JC_E_DEV_UNSUPPORTED;
  }
  if (entry->mmio_size < 0x007Cu) {
    return JC_E_DEV_UNSUPPORTED;
  }
  pic->base = entry->mmio_base.lo;
  pic->use_mmio = 1u;
  return JC_E_OK;
}

jc_u32 jc_carbonkio_pic_pending(jc_carbonkio_pic *pic) {
  if (!pic) {
    return 0u;
  }
  return jc_mmio_read32(pic->base, JC_PIC_IRQ_PENDING_OFF);
}
