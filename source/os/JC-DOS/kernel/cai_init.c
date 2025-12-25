#include "cai_init.h"

#include "bios_services.h"
#include "handoff.h"
#include "jc_cai.h"
#include "jc_config.h"
#include "jc_fpu.h"
#include "log.h"

jc_error_t jc_dos_cai_init(void) {
  jc_error_t err;

  jc_cai_set_timer(jc_bios_timer_ticks, jc_bios_timer_tick_hz);
  err = jc_cai_init(jc_dos_bdt(), jc_dos_capset());

#if JC_CFG_VERBOSE_HW
  if (err == JC_E_OK) {
    jc_dos_log("CAI READY ");
    jc_dos_log(jc_cai_is_mock() ? "MOCK" : "HW");
    jc_dos_log("\r\n");
  } else {
    jc_dos_log("CAI OFF ");
    jc_dos_log_hex16((jc_u16)err);
    jc_dos_log("\r\n");
  }
#endif

  return err;
}

jc_error_t jc_dos_fpu_init(void) {
  jc_error_t err;

  err = jc_fpu_init(jc_dos_bdt(), jc_dos_capset());

#if JC_CFG_VERBOSE_HW
  if (err == JC_E_OK) {
    jc_dos_log("FPU ");
    jc_dos_log(jc_fpu_has_hw() ? "HW" : "SOFT");
    jc_dos_log("\r\n");
  } else {
    jc_dos_log("FPU OFF ");
    jc_dos_log_hex16((jc_u16)err);
    jc_dos_log("\r\n");
  }
#endif

  return err;
}
