#include "jc_pal.h"

#include "jc_block.h"
#include "jc_bsp.h"
#include "jc_capset.h"
#include "jc_component.h"
#include "jc_console.h"
#include "jc_contracts_autogen.h"
#include "jc_discovery.h"
#include "jc_timer.h"
#include "jc_util.h"
#include "jc_bdt.h"

static jc_bdt_index g_carbon_bdt;
static jc_capset_v1 g_carbon_capset;

typedef struct {
  jc_mem_region_header_v1 header;
  jc_mem_region_entry_v1 entries[1];
} jc_pal_carbon_mem_table;

static jc_pal_carbon_mem_table g_carbon_mem;
static char g_platform_name[17];


static jc_error_t pal_carbon_console_write(void *ctx,
                                           const char *data,
                                           jc_u32 len) {
  jc_u32 i;
  (void)ctx;
  if (!data) {
    return JC_E_INTERNAL_ASSERT;
  }
  for (i = 0; i < len; ++i) {
    jc_error_t err = jc_console_putc(data[i]);
    if (err != JC_E_OK) {
      return err;
    }
  }
  return JC_E_OK;
}

static jc_error_t pal_carbon_console_read(void *ctx,
                                          char *out,
                                          jc_u32 len,
                                          jc_u32 *out_len) {
  jc_error_t err;
  (void)ctx;
  if (!out || len == 0u) {
    return JC_E_INTERNAL_ASSERT;
  }
  err = jc_console_readline(out, len);
  if (err != JC_E_OK) {
    return err;
  }
  if (out_len) {
    *out_len = jc_strlen(out);
  }
  return JC_E_OK;
}

static jc_error_t pal_carbon_console_flush(void *ctx) {
  (void)ctx;
  return JC_E_OK;
}

static jc_error_t pal_carbon_block_read(void *ctx,
                                        jc_u32 lba,
                                        jc_u8 *buf,
                                        jc_u16 count512) {
  (void)ctx;
  return jc_blk_read(lba, buf, count512);
}

static jc_error_t pal_carbon_block_write(void *ctx,
                                         jc_u32 lba,
                                         const jc_u8 *buf,
                                         jc_u16 count512) {
  (void)ctx;
  return jc_blk_write(lba, buf, count512);
}

static jc_error_t pal_carbon_block_get_params(void *ctx,
                                              jc_pal_block_params *out_params) {
  jc_block_params params;
  jc_error_t err;
  (void)ctx;
  if (!out_params) {
    return JC_E_INTERNAL_ASSERT;
  }
  err = jc_blk_get_params(&params);
  if (err != JC_E_OK) {
    return err;
  }
  out_params->block_size_bytes = params.block_size_bytes;
  out_params->max_sectors_per_op = params.max_sectors_per_op;
  out_params->total_sectors = params.total_sectors;
  out_params->timeout_ticks = params.timeout_ticks;
  return JC_E_OK;
}

static jc_u64 pal_carbon_timer_ticks(void *ctx) {
  (void)ctx;
  return jc_timer_ticks();
}

static jc_u32 pal_carbon_timer_hz(void *ctx) {
  (void)ctx;
  return jc_timer_tick_hz();
}

static void pal_carbon_timer_sleep(void *ctx, jc_u32 ticks) {
  (void)ctx;
  (void)ticks;
}

static const jc_mem_region_header_v1 *pal_carbon_memmap_get(void *ctx) {
  (void)ctx;
  return &g_carbon_mem.header;
}

static void pal_carbon_build_memmap(void) {
  g_carbon_mem.header.signature = JC_MAGIC_MEM_REGION_HEADER;
  g_carbon_mem.header.header_version = 1;
  g_carbon_mem.header.header_size = (jc_u16)sizeof(jc_mem_region_header_v1);
  g_carbon_mem.header.entry_size = (jc_u16)sizeof(jc_mem_region_entry_v1);
  g_carbon_mem.header.entry_count = 1;
  g_carbon_mem.header.total_size = (jc_u32)sizeof(g_carbon_mem);
  g_carbon_mem.entries[0].region_kind = JC_MEM_REGION_KIND_RAM;
  g_carbon_mem.entries[0].region_attrs = JC_MEM_ATTR_CACHEABLE_MASK;
  g_carbon_mem.entries[0].reserved0 = 0;
  g_carbon_mem.entries[0].base_addr =
      jc_u64_make((jc_u32)jc_bsp_tpa_base, 0);
  g_carbon_mem.entries[0].size_bytes =
      jc_u64_make((jc_u32)jc_bsp_tpa_size, 0);
  g_carbon_mem.entries[0].reserved1 = 0;
}

static void pal_carbon_copy_platform_name(void) {
  jc_u32 i;
  for (i = 0; i < sizeof(g_platform_name) - 1u; ++i) {
    char c = (char)jc_platform_desc.name[i];
    g_platform_name[i] = c;
    if (c == '\0') {
      break;
    }
  }
  g_platform_name[sizeof(g_platform_name) - 1u] = '\0';
  if (g_platform_name[0] == '\0') {
    g_platform_name[0] = 'p';
    g_platform_name[1] = 'a';
    g_platform_name[2] = 'l';
    g_platform_name[3] = '_';
    g_platform_name[4] = 'c';
    g_platform_name[5] = 'a';
    g_platform_name[6] = 'r';
    g_platform_name[7] = 'b';
    g_platform_name[8] = 'o';
    g_platform_name[9] = 'n';
    g_platform_name[10] = '\0';
  }
}

static const jc_pal_console_vtable g_carbon_console_vtable = {
    pal_carbon_console_write, pal_carbon_console_read,
    pal_carbon_console_flush};
static const jc_pal_block_vtable g_carbon_block_vtable = {
    pal_carbon_block_read, pal_carbon_block_write,
    pal_carbon_block_get_params};
static const jc_pal_timer_vtable g_carbon_timer_vtable = {
    pal_carbon_timer_ticks, pal_carbon_timer_hz, pal_carbon_timer_sleep};
static const jc_pal_memmap_vtable g_carbon_memmap_vtable = {
    pal_carbon_memmap_get};

static jc_error_t jc_pal_carbon_init(jc_pal_desc *out_desc) {
  const jc_bsp_anchor_v1 *anchor = 0;
  const jc_discovery_table_v1 *discovery = 0;
  jc_error_t err;

  if (!out_desc) {
    return JC_E_INTERNAL_ASSERT;
  }

  err = jc_discovery_init(&anchor, &discovery);
  if (err != JC_E_OK) {
    return err;
  }

  err = jc_bdt_init(&g_carbon_bdt, discovery->bdt_ptr);
  if (err != JC_E_OK) {
    return err;
  }

  err = jc_capset_init(&g_carbon_capset, discovery, &g_carbon_bdt);
  if (err != JC_E_OK) {
    return err;
  }

  pal_carbon_build_memmap();
  g_carbon_capset.mem_region_table_ptr =
      jc_u64_make((jc_u32)(unsigned long)&g_carbon_mem.header, 0);

  pal_carbon_copy_platform_name();

  out_desc->platform_id = g_platform_name;
  out_desc->platform_version = "pal_carbon-v1";
  out_desc->platform_caps =
      g_carbon_capset.periph_features[0] &
      (JC_CAP_HAS_V86 | JC_CAP_HAS_ROMWBW | JC_CAP_HAS_LOCAL_VIDEO |
       JC_CAP_HAS_PAGING | JC_CAP_HAS_IRQ);
  out_desc->platform_flags = 0;
  out_desc->bdt = g_carbon_bdt.header;
  out_desc->capset = &g_carbon_capset;

  out_desc->console.vtable = &g_carbon_console_vtable;
  out_desc->console.ctx = 0;
  out_desc->block.vtable = &g_carbon_block_vtable;
  out_desc->block.ctx = 0;
  out_desc->timer.vtable = &g_carbon_timer_vtable;
  out_desc->timer.ctx = 0;
  out_desc->memmap.vtable = &g_carbon_memmap_vtable;
  out_desc->memmap.ctx = 0;
  out_desc->keyboard.vtable = 0;
  out_desc->video.vtable = 0;
  out_desc->rtc.vtable = 0;
  out_desc->dma_sync.vtable = 0;
  return JC_E_OK;
}

void jc_pal_carbon_bind(void) { jc_pal_register(jc_pal_carbon_init); }

static const jc_component_vtable g_pal_carbon_vtable = {0, 0};

const jc_component_desc JC_COMPONENT_DESC = {
    JC_COMPONENT_ID_PAL_CARBON,
    1,
    0,
    1,
    0,
    0,
    &g_pal_carbon_vtable,
    "pal_carbon"};
