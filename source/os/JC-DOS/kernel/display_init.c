#include "display_init.h"

#include "bios_services.h"
#include "handoff.h"
#include "jc_config.h"
#include "jc_display.h"
#include "video_backends.h"

jc_error_t jc_dos_display_init(void) {
  const jc_bios_services_v1 *services = jc_bios_services();
  jc_error_t err;

  if (JC_CFG_ENABLE_DISPLAY == 0) {
    return JC_E_DEV_UNSUPPORTED;
  }
  if (!services || !services->console_putc || !services->console_write) {
    return JC_E_INTERNAL_ASSERT;
  }

  err = jc_display_init_vt100(services->console_putc, services->console_write);
  if (err != JC_E_OK) {
    return err;
  }

#if JC_CFG_ENABLE_DISPLAY_BACKENDS
  {
    const jc_bdt_header_v1 *bdt = jc_dos_bdt();
    jc_display_backend backend;

    err = jc_video_mc6845_probe(bdt, &backend);
    if (err == JC_E_OK) {
      return jc_display_set_backend(&backend);
    }

    err = jc_video_mda_probe(bdt, &backend);
    if (err == JC_E_OK) {
      return jc_display_set_backend(&backend);
    }

    err = jc_video_cga_ega_vga_probe(bdt, &backend);
    if (err == JC_E_OK) {
      return jc_display_set_backend(&backend);
    }

    err = jc_video_tms9918_probe(bdt, &backend);
    if (err == JC_E_OK) {
      return jc_display_set_backend(&backend);
    }

    err = jc_video_v99x8_probe(bdt, &backend);
    if (err == JC_E_OK) {
      return jc_display_set_backend(&backend);
    }
  }
#endif

  return JC_E_OK;
}
