#include "pal_pcbios.h"

#include "jc_component.h"
#include "jc_contracts_autogen.h"
#include "jc_pal.h"
#include "jc_util.h"

#define JC_PAL_PCBIOS_DEV_COUNT 3u

static const jc_pal_pcbios_hooks *g_pcbios_hooks;
static jc_capset_v1 g_pcbios_capset;

#define JC_PAL_PCBIOS_BDT_BYTES                               \
  (sizeof(jc_bdt_header_v1) +                                \
   (JC_PAL_PCBIOS_DEV_COUNT * sizeof(jc_bdt_entry_v1)) +      \
   sizeof(jc_bdt_footer_v1))

static jc_u8 g_pcbios_bdt_blob[JC_PAL_PCBIOS_BDT_BYTES];

typedef struct {
  jc_mem_region_header_v1 header;
  jc_mem_region_entry_v1 entries[2];
} jc_pal_pcbios_mem_table;

static const jc_pal_pcbios_mem_table g_pcbios_mem = {
    {JC_MAGIC_MEM_REGION_HEADER,
     1,
     (jc_u16)sizeof(jc_mem_region_header_v1),
     (jc_u16)sizeof(jc_mem_region_entry_v1),
     2,
     (jc_u32)sizeof(jc_pal_pcbios_mem_table)},
    {{JC_MEM_REGION_KIND_RAM,
      JC_MEM_ATTR_CACHEABLE_MASK,
      0,
      {0x00000000u, 0u},
      {0x000A0000u, 0u},
      0},
     {JC_MEM_REGION_KIND_ROM,
      JC_MEM_ATTR_CACHEABLE_MASK,
      0,
      {0x000F0000u, 0u},
      {0x00010000u, 0u},
      0}}};

void jc_pal_pcbios_set_hooks(const jc_pal_pcbios_hooks *hooks) {
  g_pcbios_hooks = hooks;
}

static jc_error_t pcbios_console_write(void *ctx,
                                       const char *data,
                                       jc_u32 len) {
  const jc_pal_pcbios_hooks *hooks = (const jc_pal_pcbios_hooks *)ctx;
  if (!hooks || !hooks->console_write) {
    return JC_E_DEV_UNSUPPORTED;
  }
  return hooks->console_write(hooks->ctx, data, len);
}

static jc_error_t pcbios_console_read(void *ctx,
                                      char *out,
                                      jc_u32 len,
                                      jc_u32 *out_len) {
  const jc_pal_pcbios_hooks *hooks = (const jc_pal_pcbios_hooks *)ctx;
  if (!hooks || !hooks->console_read) {
    return JC_E_DEV_UNSUPPORTED;
  }
  return hooks->console_read(hooks->ctx, out, len, out_len);
}

static jc_error_t pcbios_block_read(void *ctx,
                                    jc_u32 lba,
                                    jc_u8 *buf,
                                    jc_u16 count512) {
  const jc_pal_pcbios_hooks *hooks = (const jc_pal_pcbios_hooks *)ctx;
  if (!hooks || !hooks->block_read) {
    return JC_E_DEV_UNSUPPORTED;
  }
  return hooks->block_read(hooks->ctx, lba, buf, count512);
}

static jc_error_t pcbios_block_write(void *ctx,
                                     jc_u32 lba,
                                     const jc_u8 *buf,
                                     jc_u16 count512) {
  const jc_pal_pcbios_hooks *hooks = (const jc_pal_pcbios_hooks *)ctx;
  if (!hooks || !hooks->block_write) {
    return JC_E_DEV_UNSUPPORTED;
  }
  return hooks->block_write(hooks->ctx, lba, buf, count512);
}

static jc_error_t pcbios_block_get_params(void *ctx,
                                          jc_pal_block_params *out_params) {
  const jc_pal_pcbios_hooks *hooks = (const jc_pal_pcbios_hooks *)ctx;
  if (!hooks || !hooks->block_get_params) {
    return JC_E_DEV_UNSUPPORTED;
  }
  return hooks->block_get_params(hooks->ctx, out_params);
}

static jc_u64 pcbios_timer_ticks(void *ctx) {
  const jc_pal_pcbios_hooks *hooks = (const jc_pal_pcbios_hooks *)ctx;
  if (!hooks || !hooks->timer_ticks) {
    jc_u64 zero = {0u, 0u};
    return zero;
  }
  return hooks->timer_ticks(hooks->ctx);
}

static jc_u32 pcbios_timer_hz(void *ctx) {
  const jc_pal_pcbios_hooks *hooks = (const jc_pal_pcbios_hooks *)ctx;
  if (!hooks || !hooks->timer_hz) {
    return 0;
  }
  return hooks->timer_hz(hooks->ctx);
}

static jc_error_t pcbios_keyboard_read(void *ctx,
                                       jc_pal_key_event *out_event) {
  const jc_pal_pcbios_hooks *hooks = (const jc_pal_pcbios_hooks *)ctx;
  if (!hooks || !hooks->keyboard_read) {
    return JC_E_DEV_UNSUPPORTED;
  }
  return hooks->keyboard_read(hooks->ctx, out_event);
}

static int pcbios_keyboard_poll(void *ctx, jc_pal_key_event *out_event) {
  const jc_pal_pcbios_hooks *hooks = (const jc_pal_pcbios_hooks *)ctx;
  if (!hooks || !hooks->keyboard_poll) {
    return 0;
  }
  return hooks->keyboard_poll(hooks->ctx, out_event);
}

static const jc_mem_region_header_v1 *pcbios_memmap_get(void *ctx) {
  const jc_pal_pcbios_hooks *hooks = (const jc_pal_pcbios_hooks *)ctx;
  if (hooks && hooks->memmap_get) {
    return hooks->memmap_get(hooks->ctx);
  }
  return &g_pcbios_mem.header;
}

static const jc_pal_console_vtable g_pcbios_console_vtable = {
    pcbios_console_write, pcbios_console_read, 0};
static const jc_pal_block_vtable g_pcbios_block_vtable = {
    pcbios_block_read, pcbios_block_write, pcbios_block_get_params};
static const jc_pal_timer_vtable g_pcbios_timer_vtable = {pcbios_timer_ticks,
                                                          pcbios_timer_hz, 0};
static const jc_pal_keyboard_vtable g_pcbios_keyboard_vtable = {
    pcbios_keyboard_read, pcbios_keyboard_poll};
static const jc_pal_memmap_vtable g_pcbios_memmap_vtable = {
    pcbios_memmap_get};

static jc_error_t pcbios_build_bdt(jc_bdt_header_v1 **out_header) {
  jc_bdt_header_v1 *header = (jc_bdt_header_v1 *)g_pcbios_bdt_blob;
  jc_bdt_entry_v1 *entries = (jc_bdt_entry_v1 *)(g_pcbios_bdt_blob +
                                                 sizeof(jc_bdt_header_v1));
  jc_bdt_footer_v1 *footer = (jc_bdt_footer_v1 *)(g_pcbios_bdt_blob +
                                                  JC_PAL_PCBIOS_BDT_BYTES -
                                                  sizeof(jc_bdt_footer_v1));
  jc_u32 total_size = (jc_u32)sizeof(g_pcbios_bdt_blob);
  jc_u32 crc;

  jc_memset(g_pcbios_bdt_blob, 0, (jc_u32)sizeof(g_pcbios_bdt_blob));
  header->signature = JC_MAGIC_BDT;
  header->header_version = JC_BDT_HEADER_V1_VERSION;
  header->header_size = (jc_u16)sizeof(jc_bdt_header_v1);
  header->entry_size = (jc_u16)sizeof(jc_bdt_entry_v1);
  header->entry_count = JC_PAL_PCBIOS_DEV_COUNT;
  header->total_size = total_size;

  entries[0].desc_version = JC_BDT_ENTRY_V1_VERSION;
  entries[0].desc_size_bytes = JC_BDT_ENTRY_V1_SIZE;
  entries[0].class_id = JC_DEVCLASS_UART;
  entries[0].instance_id = 0;
  entries[0].device_version = 1;
  entries[0].caps0 = JC_DEV_COMPAT_POLLING_MASK;

  entries[1].desc_version = JC_BDT_ENTRY_V1_VERSION;
  entries[1].desc_size_bytes = JC_BDT_ENTRY_V1_SIZE;
  entries[1].class_id = JC_DEVCLASS_TIMER;
  entries[1].instance_id = 0;
  entries[1].device_version = 1;
  entries[1].caps0 = JC_DEV_COMPAT_POLLING_MASK;

  entries[2].desc_version = JC_BDT_ENTRY_V1_VERSION;
  entries[2].desc_size_bytes = JC_BDT_ENTRY_V1_SIZE;
  entries[2].class_id = JC_DEVCLASS_STORAGE;
  entries[2].instance_id = 0;
  entries[2].device_version = 1;
  entries[2].caps0 = JC_DEV_COMPAT_POLLING_MASK;
  entries[2].block_sector_size = 512u;

  crc = jc_crc32((const jc_u8 *)header,
                 total_size - (jc_u32)sizeof(jc_bdt_footer_v1));
  footer->crc32 = crc;
  *out_header = header;
  return JC_E_OK;
}

static jc_error_t pcbios_build_capset(const jc_pal_pcbios_hooks *hooks,
                                      const jc_bdt_header_v1 *bdt,
                                      const jc_mem_region_header_v1 *memmap) {
  jc_u32 platform_caps = 0u;
  jc_memset(&g_pcbios_capset, 0, sizeof(g_pcbios_capset));
  g_pcbios_capset.signature = JC_MAGIC_CAPSET;
  g_pcbios_capset.version = JC_CAPSET_V1_VERSION;
  g_pcbios_capset.size_bytes = JC_CAPSET_V1_SIZE;
  if (hooks) {
    g_pcbios_capset.cpu_ladder_id = hooks->cpu_ladder_id;
    g_pcbios_capset.fpu_ladder_id = hooks->fpu_ladder_id;
    g_pcbios_capset.presented_cpu_tier = hooks->presented_cpu_tier;
    g_pcbios_capset.presented_fpu_tier = hooks->presented_fpu_tier;
    g_pcbios_capset.profile_id = hooks->profile_id;
    platform_caps |= hooks->platform_caps;
  }
  g_pcbios_capset.periph_features[0] =
      JC_PERIPH_FEAT_BDT_MASK | JC_PERIPH_FEAT_DEVICE_MODEL_MASK |
      platform_caps;
  g_pcbios_capset.bdt_ptr = jc_u64_make((jc_u32)(unsigned long)bdt, 0);
  if (memmap) {
    g_pcbios_capset.mem_region_table_ptr =
        jc_u64_make((jc_u32)(unsigned long)memmap, 0);
  }
  g_pcbios_capset.max_devices = JC_PAL_PCBIOS_DEV_COUNT;
  g_pcbios_capset.max_bdt_entries = JC_PAL_PCBIOS_DEV_COUNT;
  g_pcbios_capset.max_irq_routes = 0;
  return JC_E_OK;
}

static jc_error_t jc_pal_pcbios_init(jc_pal_desc *out_desc) {
  jc_bdt_header_v1 *bdt = 0;
  const jc_mem_region_header_v1 *memmap;
  jc_error_t err;

  if (!out_desc) {
    return JC_E_INTERNAL_ASSERT;
  }
  if (!g_pcbios_hooks || !g_pcbios_hooks->platform_id ||
      !g_pcbios_hooks->platform_version) {
    return JC_E_DEV_UNSUPPORTED;
  }

  err = pcbios_build_bdt(&bdt);
  if (err != JC_E_OK) {
    return err;
  }

  memmap = pcbios_memmap_get((void *)g_pcbios_hooks);
  err = pcbios_build_capset(g_pcbios_hooks, bdt, memmap);
  if (err != JC_E_OK) {
    return err;
  }

  out_desc->platform_id = g_pcbios_hooks->platform_id;
  out_desc->platform_version = g_pcbios_hooks->platform_version;
  out_desc->platform_caps =
      g_pcbios_capset.periph_features[0] &
      (JC_CAP_HAS_V86 | JC_CAP_HAS_LOCAL_VIDEO | JC_CAP_HAS_PAGING |
       JC_CAP_HAS_IRQ);
  out_desc->platform_flags = JC_PAL_FLAG_NO_PROBE;
  out_desc->bdt = bdt;
  out_desc->capset = &g_pcbios_capset;

  out_desc->console.vtable = &g_pcbios_console_vtable;
  out_desc->console.ctx = (void *)g_pcbios_hooks;
  out_desc->block.vtable = &g_pcbios_block_vtable;
  out_desc->block.ctx = (void *)g_pcbios_hooks;
  out_desc->timer.vtable = &g_pcbios_timer_vtable;
  out_desc->timer.ctx = (void *)g_pcbios_hooks;
  out_desc->memmap.vtable = &g_pcbios_memmap_vtable;
  out_desc->memmap.ctx = (void *)g_pcbios_hooks;
  out_desc->keyboard.vtable = &g_pcbios_keyboard_vtable;
  out_desc->keyboard.ctx = (void *)g_pcbios_hooks;
  out_desc->video.vtable = 0;
  out_desc->rtc.vtable = 0;
  out_desc->dma_sync.vtable = 0;
  return JC_E_OK;
}

void jc_pal_pcbios_bind(void) { jc_pal_register(jc_pal_pcbios_init); }

static const jc_component_vtable g_pal_pcbios_vtable = {0, 0};

const jc_component_desc JC_COMPONENT_DESC = {
    JC_COMPONENT_ID_PAL_PCBIOS,
    1,
    0,
    1,
    0,
    0,
    &g_pal_pcbios_vtable,
    "pal_pcbios"};
