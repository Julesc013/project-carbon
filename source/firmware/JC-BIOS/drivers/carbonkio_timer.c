#include "jc_carbonkio.h"

#include "jc_contracts_autogen.h"
#include "jc_util.h"

#define JC_TIMER_TICK_LO_OFF 0x0040u
#define JC_TIMER_TICK_HI_OFF 0x0044u

static jc_u32 jc_mmio_read32(jc_u32 base, jc_u32 off) {
  volatile jc_u32 *reg = (volatile jc_u32 *)(unsigned long)(base + off);
  return *reg;
}

jc_error_t jc_carbonkio_timer_init(jc_carbonkio_timer *timer,
                                   const jc_bdt_entry_v1 *entry) {
  if (!timer || !entry) {
    return JC_E_INTERNAL_ASSERT;
  }
  if (entry->mmio_base.hi != 0u || entry->mmio_base.lo == 0u) {
    return JC_E_DEV_UNSUPPORTED;
  }
  if (entry->mmio_size < 0x0068u) {
    return JC_E_DEV_UNSUPPORTED;
  }
  timer->base = entry->mmio_base.lo;
  timer->use_mmio = 1u;
  timer->tick_hz = entry->caps0;
  return JC_E_OK;
}

jc_u64 jc_carbonkio_timer_ticks(jc_carbonkio_timer *timer) {
  jc_u32 hi0;
  jc_u32 hi1;
  jc_u32 lo;
  jc_u64 out;
  if (!timer) {
    return jc_u64_make(0, 0);
  }
  hi0 = jc_mmio_read32(timer->base, JC_TIMER_TICK_HI_OFF);
  lo = jc_mmio_read32(timer->base, JC_TIMER_TICK_LO_OFF);
  hi1 = jc_mmio_read32(timer->base, JC_TIMER_TICK_HI_OFF);
  if (hi0 != hi1) {
    lo = jc_mmio_read32(timer->base, JC_TIMER_TICK_LO_OFF);
  }
  out.lo = lo;
  out.hi = hi1;
  return out;
}
