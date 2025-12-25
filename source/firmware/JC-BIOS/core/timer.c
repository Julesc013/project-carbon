#include "jc_timer.h"

#include "jc_bdt.h"
#include "jc_bios.h"
#include "jc_carbonkio.h"
#include "jc_contracts_autogen.h"
#include "jc_util.h"

static jc_carbonkio_timer g_timer;
static int g_timer_ready = 0;

jc_error_t jc_timer_init(void) {
  const jc_bdt_index *bdt = 0;
  const jc_bdt_entry_v1 *entry = 0;
  jc_error_t err;

  bdt = jc_boot_bdt_index();
  if (!bdt) {
    return JC_E_BDT_BAD_SIZE;
  }
  entry = jc_bdt_find(bdt, JC_DEVCLASS_TIMER, 0);
  if (!entry) {
    return JC_E_DEV_NOT_FOUND;
  }
  err = jc_carbonkio_timer_init(&g_timer, entry);
  if (err == JC_E_OK) {
    g_timer_ready = 1;
  }
  return err;
}

jc_u64 jc_timer_ticks(void) {
  if (!g_timer_ready) {
    return jc_u64_make(0, 0);
  }
  return jc_carbonkio_timer_ticks(&g_timer);
}

jc_u32 jc_timer_tick_hz(void) {
  if (!g_timer_ready) {
    return 0;
  }
  return g_timer.tick_hz;
}

jc_u64 jc_timer_deadline_from_now(jc_u32 ticks) {
  return jc_u64_add_u32(jc_timer_ticks(), ticks);
}

int jc_timer_expired(jc_u64 deadline) {
  return jc_u64_cmp(jc_timer_ticks(), deadline) >= 0;
}
