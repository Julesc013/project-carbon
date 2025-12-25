#include "jc_carbonkio.h"

#define JC_PIC_IRQ_ENABLE_OFF 0x0070u
#define JC_PIC_IRQ_PENDING_OFF 0x0074u
#define JC_PIC_IRQ_MASK_OFF 0x0078u

static jc_u32 jc_mmio_read32(jc_u32 base, jc_u32 off) {
  volatile jc_u32 *reg = (volatile jc_u32 *)(unsigned long)(base + off);
  return *reg;
}

static void jc_mmio_write32(jc_u32 base, jc_u32 off, jc_u32 value) {
  volatile jc_u32 *reg = (volatile jc_u32 *)(unsigned long)(base + off);
  *reg = value;
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

jc_error_t jc_carbonkio_pic_write_enable(jc_carbonkio_pic *pic, jc_u32 value) {
  if (!pic) {
    return JC_E_INTERNAL_ASSERT;
  }
  jc_mmio_write32(pic->base, JC_PIC_IRQ_ENABLE_OFF, value);
  return JC_E_OK;
}

jc_error_t jc_carbonkio_pic_write_mask(jc_carbonkio_pic *pic, jc_u32 value) {
  if (!pic) {
    return JC_E_INTERNAL_ASSERT;
  }
  jc_mmio_write32(pic->base, JC_PIC_IRQ_MASK_OFF, value);
  return JC_E_OK;
}

jc_error_t jc_carbonkio_pic_ack(jc_carbonkio_pic *pic, jc_u32 value) {
  (void)pic;
  (void)value;
  return JC_E_OK;
}
