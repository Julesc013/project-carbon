#include "pal_romwbw.h"

#include "jc_component.h"
#include "jc_pal.h"

static const jc_pal_romwbw_hooks *g_romwbw_hooks;

void jc_pal_romwbw_set_hooks(const jc_pal_romwbw_hooks *hooks) {
  g_romwbw_hooks = hooks;
}

static jc_error_t romwbw_console_write(void *ctx,
                                       const char *data,
                                       jc_u32 len) {
  const jc_pal_romwbw_hooks *hooks = (const jc_pal_romwbw_hooks *)ctx;
  if (!hooks || !hooks->console_write) {
    return JC_E_DEV_UNSUPPORTED;
  }
  return hooks->console_write(hooks->ctx, data, len);
}

static jc_error_t romwbw_console_read(void *ctx,
                                      char *out,
                                      jc_u32 len,
                                      jc_u32 *out_len) {
  const jc_pal_romwbw_hooks *hooks = (const jc_pal_romwbw_hooks *)ctx;
  if (!hooks || !hooks->console_read) {
    return JC_E_DEV_UNSUPPORTED;
  }
  return hooks->console_read(hooks->ctx, out, len, out_len);
}

static jc_error_t romwbw_block_read(void *ctx,
                                    jc_u32 lba,
                                    jc_u8 *buf,
                                    jc_u16 count512) {
  const jc_pal_romwbw_hooks *hooks = (const jc_pal_romwbw_hooks *)ctx;
  if (!hooks || !hooks->block_read) {
    return JC_E_DEV_UNSUPPORTED;
  }
  return hooks->block_read(hooks->ctx, lba, buf, count512);
}

static jc_error_t romwbw_block_write(void *ctx,
                                     jc_u32 lba,
                                     const jc_u8 *buf,
                                     jc_u16 count512) {
  const jc_pal_romwbw_hooks *hooks = (const jc_pal_romwbw_hooks *)ctx;
  if (!hooks || !hooks->block_write) {
    return JC_E_DEV_UNSUPPORTED;
  }
  return hooks->block_write(hooks->ctx, lba, buf, count512);
}

static jc_error_t romwbw_block_get_params(void *ctx,
                                          jc_pal_block_params *out_params) {
  const jc_pal_romwbw_hooks *hooks = (const jc_pal_romwbw_hooks *)ctx;
  if (!hooks || !hooks->block_get_params) {
    return JC_E_DEV_UNSUPPORTED;
  }
  return hooks->block_get_params(hooks->ctx, out_params);
}

static jc_u64 romwbw_timer_ticks(void *ctx) {
  const jc_pal_romwbw_hooks *hooks = (const jc_pal_romwbw_hooks *)ctx;
  if (!hooks || !hooks->timer_ticks) {
    jc_u64 zero = {0u, 0u};
    return zero;
  }
  return hooks->timer_ticks(hooks->ctx);
}

static jc_u32 romwbw_timer_hz(void *ctx) {
  const jc_pal_romwbw_hooks *hooks = (const jc_pal_romwbw_hooks *)ctx;
  if (!hooks || !hooks->timer_hz) {
    return 0;
  }
  return hooks->timer_hz(hooks->ctx);
}

static const jc_mem_region_header_v1 *romwbw_memmap_get(void *ctx) {
  const jc_pal_romwbw_hooks *hooks = (const jc_pal_romwbw_hooks *)ctx;
  if (!hooks || !hooks->memmap_get) {
    return 0;
  }
  return hooks->memmap_get(hooks->ctx);
}

static const jc_pal_console_vtable g_romwbw_console_vtable = {
    romwbw_console_write, romwbw_console_read, 0};
static const jc_pal_block_vtable g_romwbw_block_vtable = {
    romwbw_block_read, romwbw_block_write, romwbw_block_get_params};
static const jc_pal_timer_vtable g_romwbw_timer_vtable = {romwbw_timer_ticks,
                                                          romwbw_timer_hz, 0};
static const jc_pal_memmap_vtable g_romwbw_memmap_vtable = {
    romwbw_memmap_get};

static jc_error_t jc_pal_romwbw_init(jc_pal_desc *out_desc) {
  if (!out_desc) {
    return JC_E_INTERNAL_ASSERT;
  }
  if (!g_romwbw_hooks || !g_romwbw_hooks->platform_id ||
      !g_romwbw_hooks->platform_version) {
    return JC_E_DEV_UNSUPPORTED;
  }
  if (!g_romwbw_hooks->bdt || !g_romwbw_hooks->capset ||
      !g_romwbw_hooks->memmap_get) {
    return JC_E_DEV_UNSUPPORTED;
  }

  out_desc->platform_id = g_romwbw_hooks->platform_id;
  out_desc->platform_version = g_romwbw_hooks->platform_version;
  out_desc->platform_caps = g_romwbw_hooks->platform_caps | JC_CAP_HAS_ROMWBW;
  out_desc->platform_flags = JC_PAL_FLAG_NO_PROBE;
  out_desc->bdt = g_romwbw_hooks->bdt;
  out_desc->capset = g_romwbw_hooks->capset;

  out_desc->console.vtable = &g_romwbw_console_vtable;
  out_desc->console.ctx = (void *)g_romwbw_hooks;
  out_desc->block.vtable = &g_romwbw_block_vtable;
  out_desc->block.ctx = (void *)g_romwbw_hooks;
  out_desc->timer.vtable = &g_romwbw_timer_vtable;
  out_desc->timer.ctx = (void *)g_romwbw_hooks;
  out_desc->memmap.vtable = &g_romwbw_memmap_vtable;
  out_desc->memmap.ctx = (void *)g_romwbw_hooks;
  return JC_E_OK;
}

void jc_pal_romwbw_bind(void) { jc_pal_register(jc_pal_romwbw_init); }

static const jc_component_vtable g_pal_romwbw_vtable = {0, 0};

const jc_component_desc JC_COMPONENT_DESC = {
    JC_COMPONENT_ID_PAL_ROMWBW,
    1,
    0,
    1,
    0,
    0,
    &g_pal_romwbw_vtable,
    "pal_romwbw"};
