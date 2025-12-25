#include "jc_bios_services_impl.h"

#include "jc_block.h"
#include "jc_block_robust.h"
#include "jc_console.h"
#include "jc_timer.h"

static void jc_bios_reboot(void) {
  void (*reset)(void) = (void (*)(void))0x0000;
  reset();
}

static const jc_bios_services_v1 g_bios_services = {
    JC_BIOS_SERVICES_V1_SIGNATURE,
    JC_BIOS_SERVICES_V1_VERSION,
    (jc_u16)sizeof(jc_bios_services_v1),
    jc_console_putc,
    jc_console_write,
    jc_console_readline,
    jc_blk_open,
    jc_blk_read_robust,
    jc_blk_write_robust,
    jc_blk_test_timeout,
    jc_timer_ticks,
    jc_timer_tick_hz,
    jc_bios_reboot,
    0,
    0};

const jc_bios_services_v1 *jc_bios_services_get(void) {
  return &g_bios_services;
}
