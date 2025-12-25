#include "jc_carbonkio.h"

#include "jc_contracts_autogen.h"
#include "jc_util.h"

#define JC_TIMER_TICK_LO_OFF 0x0040u
#define JC_TIMER_TICK_HI_OFF 0x0044u
#define JC_TIMER0_LOAD_OFF 0x0048u
#define JC_TIMER0_CTRL_OFF 0x0050u
#define JC_TIMER0_STATUS_OFF 0x0054u

#define JC_TIMER_CTRL_ENABLE (1u << 0)
#define JC_TIMER_CTRL_AUTO_RELOAD (1u << 1)
#define JC_TIMER_CTRL_LOAD (1u << 2)
#define JC_TIMER_STATUS_EXPIRED (1u << 0)

static jc_u32 jc_mmio_read32(jc_u32 base, jc_u32 off) {
  volatile jc_u32 *reg = (volatile jc_u32 *)(unsigned long)(base + off);
  return *reg;
}

static void jc_mmio_write32(jc_u32 base, jc_u32 off, jc_u32 value) {
  volatile jc_u32 *reg = (volatile jc_u32 *)(unsigned long)(base + off);
  *reg = value;
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

jc_error_t jc_carbonkio_timer_irq_init(jc_carbonkio_timer *timer) {
  jc_u32 load;
  if (!timer) {
    return JC_E_INTERNAL_ASSERT;
  }
  load = timer->tick_hz ? timer->tick_hz : 1u;
  jc_mmio_write32(timer->base, JC_TIMER0_LOAD_OFF, load);
  jc_mmio_write32(timer->base, JC_TIMER0_CTRL_OFF,
                  JC_TIMER_CTRL_ENABLE | JC_TIMER_CTRL_AUTO_RELOAD |
                      JC_TIMER_CTRL_LOAD);
  jc_mmio_write32(timer->base, JC_TIMER0_STATUS_OFF, JC_TIMER_STATUS_EXPIRED);
  return JC_E_OK;
}

int jc_carbonkio_timer_irq_poll(jc_carbonkio_timer *timer) {
  jc_u32 status;
  if (!timer) {
    return 0;
  }
  status = jc_mmio_read32(timer->base, JC_TIMER0_STATUS_OFF);
  if ((status & JC_TIMER_STATUS_EXPIRED) == 0u) {
    return 0;
  }
  jc_mmio_write32(timer->base, JC_TIMER0_STATUS_OFF, JC_TIMER_STATUS_EXPIRED);
  return 1;
}
