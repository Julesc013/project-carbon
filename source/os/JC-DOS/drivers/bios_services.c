#include "bios_services.h"

#include "jc_display.h"

static const jc_bios_services_v1 *g_services;

jc_error_t jc_bios_services_init(const jc_bios_services_v1 *services) {
  if (!services) {
    return JC_E_INTERNAL_ASSERT;
  }
  if (services->signature != JC_BIOS_SERVICES_V1_SIGNATURE) {
    return JC_E_BOOT_BSP_BAD_SIGNATURE;
  }
  if (services->version != JC_BIOS_SERVICES_V1_VERSION ||
      services->size_bytes < sizeof(jc_bios_services_v1)) {
    return JC_E_BOOT_UNSUPPORTED_PROFILE;
  }
  g_services = services;
  return JC_E_OK;
}

const jc_bios_services_v1 *jc_bios_services(void) {
  return g_services;
}

jc_error_t jc_bios_console_putc(char c) {
  if (jc_display_is_ready()) {
    jc_error_t err = jc_display_putc(c);
    if (err == JC_E_OK) {
      return err;
    }
    if (err != JC_E_DEV_UNSUPPORTED) {
      return err;
    }
  }
  if (!g_services || !g_services->console_putc) {
    return JC_E_INTERNAL_ASSERT;
  }
  return g_services->console_putc(c);
}

jc_error_t jc_bios_console_write(const char *s) {
  if (jc_display_is_ready()) {
    jc_error_t err = jc_display_puts(s);
    if (err == JC_E_OK) {
      return err;
    }
    if (err != JC_E_DEV_UNSUPPORTED) {
      return err;
    }
  }
  if (!g_services || !g_services->console_write) {
    return JC_E_INTERNAL_ASSERT;
  }
  return g_services->console_write(s);
}

jc_error_t jc_bios_console_readline(char *buf, jc_u32 max_len) {
  if (!g_services || !g_services->console_readline) {
    return JC_E_INTERNAL_ASSERT;
  }
  return g_services->console_readline(buf, max_len);
}

jc_error_t jc_bios_block_open(jc_u16 instance) {
  if (!g_services || !g_services->block_open) {
    return JC_E_INTERNAL_ASSERT;
  }
  return g_services->block_open(instance);
}

jc_error_t jc_bios_block_read(jc_u32 lba, jc_u8 *buf, jc_u16 count512) {
  if (!g_services || !g_services->block_read) {
    return JC_E_INTERNAL_ASSERT;
  }
  return g_services->block_read(lba, buf, count512);
}

jc_error_t jc_bios_block_write(jc_u32 lba, const jc_u8 *buf,
                               jc_u16 count512) {
  if (!g_services || !g_services->block_write) {
    return JC_E_INTERNAL_ASSERT;
  }
  return g_services->block_write(lba, buf, count512);
}

jc_error_t jc_bios_block_test_timeout(jc_u32 timeout_ticks) {
  if (!g_services || !g_services->block_test_timeout) {
    return JC_E_INTERNAL_ASSERT;
  }
  return g_services->block_test_timeout(timeout_ticks);
}

jc_u64 jc_bios_timer_ticks(void) {
  jc_u64 zero;
  zero.lo = 0;
  zero.hi = 0;
  if (!g_services || !g_services->timer_ticks) {
    return zero;
  }
  return g_services->timer_ticks();
}

jc_u32 jc_bios_timer_tick_hz(void) {
  if (!g_services || !g_services->timer_tick_hz) {
    return 0;
  }
  return g_services->timer_tick_hz();
}

void jc_bios_reboot(void) {
  if (!g_services || !g_services->reboot) {
    return;
  }
  g_services->reboot();
}
