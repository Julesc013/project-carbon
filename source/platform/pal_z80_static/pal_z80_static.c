#include "pal_z80_board.h"

#include "jc_component.h"
#include "jc_contracts_autogen.h"
#include "jc_pal.h"
#include "jc_util.h"

#define JC_PAL_Z80_MAX_DEVICES 16u
#define JC_PAL_Z80_MAX_IRQ_ROUTES 32u

#define JC_PAL_Z80_MAX_BDT_BYTES                                   \
  (sizeof(jc_bdt_header_v1) +                                      \
   (JC_PAL_Z80_MAX_DEVICES * sizeof(jc_bdt_entry_v1)) +            \
   (JC_PAL_Z80_MAX_IRQ_ROUTES * sizeof(jc_bdt_irq_route_v1)) +     \
   sizeof(jc_bdt_footer_v1))

static jc_u8 g_bdt_blob[JC_PAL_Z80_MAX_BDT_BYTES];
static jc_capset_v1 g_capset;

static void jc_pal_z80_zero(void *ptr, jc_u32 len) {
  jc_u8 *out = (jc_u8 *)ptr;
  while (len--) {
    *out++ = 0;
  }
}

static jc_u16 jc_pal_z80_total_routes(const jc_pal_board_pack *pack) {
  jc_u16 total = 0;
  jc_u16 i;
  if (!pack || !pack->devices) {
    return 0;
  }
  for (i = 0; i < pack->device_count; ++i) {
    total = (jc_u16)(total + pack->devices[i].irq_route_count);
  }
  return total;
}

static jc_error_t jc_pal_z80_build_bdt(const jc_pal_board_pack *pack,
                                       jc_bdt_header_v1 **out_header,
                                       jc_u16 *out_routes) {
  jc_bdt_header_v1 *header;
  jc_bdt_entry_v1 *entries;
  jc_bdt_irq_route_v1 *routes;
  jc_bdt_footer_v1 *footer;
  jc_u32 header_size;
  jc_u32 entry_size;
  jc_u32 route_size;
  jc_u32 entry_count;
  jc_u32 total_routes;
  jc_u32 route_offset;
  jc_u32 route_index;
  jc_u32 total_size;
  jc_u32 crc;
  jc_u32 i;

  if (!pack || !out_header || !out_routes) {
    return JC_E_INTERNAL_ASSERT;
  }
  if (pack->device_count > JC_PAL_Z80_MAX_DEVICES) {
    return JC_E_BDT_BAD_SIZE;
  }

  total_routes = (jc_u32)jc_pal_z80_total_routes(pack);
  if (total_routes > JC_PAL_Z80_MAX_IRQ_ROUTES) {
    return JC_E_BDT_BAD_SIZE;
  }

  header_size = (jc_u32)sizeof(jc_bdt_header_v1);
  entry_size = (jc_u32)sizeof(jc_bdt_entry_v1);
  route_size = (jc_u32)sizeof(jc_bdt_irq_route_v1);
  entry_count = pack->device_count;
  total_size = header_size + entry_size * entry_count +
               route_size * total_routes + (jc_u32)sizeof(jc_bdt_footer_v1);

  if (total_size > (jc_u32)sizeof(g_bdt_blob)) {
    return JC_E_BDT_BAD_SIZE;
  }

  header = (jc_bdt_header_v1 *)g_bdt_blob;
  entries = (jc_bdt_entry_v1 *)(g_bdt_blob + header_size);
  routes =
      (jc_bdt_irq_route_v1 *)(g_bdt_blob + header_size + entry_size * entry_count);
  footer = (jc_bdt_footer_v1 *)(g_bdt_blob + total_size -
                                (jc_u32)sizeof(jc_bdt_footer_v1));

  jc_pal_z80_zero(g_bdt_blob, total_size);

  header->signature = JC_MAGIC_BDT;
  header->header_version = JC_BDT_HEADER_V1_VERSION;
  header->header_size = (jc_u16)header_size;
  header->entry_size = (jc_u16)entry_size;
  header->entry_count = (jc_u16)entry_count;
  header->total_size = total_size;

  route_offset = header_size + entry_size * entry_count;
  route_index = 0;
  for (i = 0; i < entry_count; ++i) {
    const jc_pal_board_device *dev = &pack->devices[i];
    jc_bdt_entry_v1 *entry = &entries[i];
    entry->desc_version = JC_BDT_ENTRY_V1_VERSION;
    entry->desc_size_bytes = JC_BDT_ENTRY_V1_SIZE;
    entry->class_id = dev->class_id;
    entry->subclass_id = dev->subclass_id;
    entry->instance_id = dev->instance_id;
    entry->device_version = dev->device_version;
    entry->caps0 = dev->caps0;
    entry->caps1 = dev->caps1;
    entry->mmio_base = dev->mmio_base;
    entry->mmio_size = dev->mmio_size;
    entry->io_port_base = dev->io_port_base;
    entry->io_port_size = dev->io_port_size;
    entry->block_sector_size = dev->block_sector_size;
    entry->cai_queue_count = dev->cai_queue_count;
    entry->cai_doorbell_offset = dev->cai_doorbell_offset;
    entry->aux_ptr = dev->aux_ptr;
    entry->aux_size = dev->aux_size;
    entry->aux_type = dev->aux_type;
    if (dev->irq_route_count && dev->irq_routes) {
      jc_u32 routes_bytes =
          (jc_u32)dev->irq_route_count * (jc_u32)sizeof(jc_bdt_irq_route_v1);
      jc_u32 offset = route_offset + route_index * route_size;
      entry->irq_route_offset = (jc_u16)offset;
      entry->irq_route_count = dev->irq_route_count;
      jc_memcpy(&routes[route_index], dev->irq_routes, routes_bytes);
      route_index += dev->irq_route_count;
    } else {
      entry->irq_route_offset = 0;
      entry->irq_route_count = 0;
    }
  }

  crc = jc_crc32((const jc_u8 *)header,
                 total_size - (jc_u32)sizeof(jc_bdt_footer_v1));
  footer->crc32 = crc;

  *out_header = header;
  *out_routes = (jc_u16)total_routes;
  return JC_E_OK;
}

static jc_error_t jc_pal_z80_build_capset(const jc_pal_board_pack *pack,
                                          const jc_bdt_header_v1 *bdt,
                                          jc_u16 total_routes) {
  jc_u32 periph0;
  jc_pal_z80_zero(&g_capset, sizeof(g_capset));
  g_capset.signature = JC_MAGIC_CAPSET;
  g_capset.version = JC_CAPSET_V1_VERSION;
  g_capset.size_bytes = JC_CAPSET_V1_SIZE;
  g_capset.cpu_ladder_id = pack->cpu_ladder_id;
  g_capset.fpu_ladder_id = pack->fpu_ladder_id;
  g_capset.presented_cpu_tier = pack->presented_cpu_tier;
  g_capset.presented_fpu_tier = pack->presented_fpu_tier;
  g_capset.profile_id = pack->profile_id;
  periph0 = JC_PERIPH_FEAT_BDT_MASK | JC_PERIPH_FEAT_DEVICE_MODEL_MASK |
            pack->platform_caps;
  g_capset.periph_features[0] = periph0;
  g_capset.bdt_ptr = jc_u64_make((jc_u32)(unsigned long)bdt, 0);
  if (pack->mem_regions) {
    g_capset.mem_region_table_ptr =
        jc_u64_make((jc_u32)(unsigned long)pack->mem_regions, 0);
  } else {
    g_capset.mem_region_table_ptr = jc_u64_make(0, 0);
  }
  g_capset.max_devices = pack->device_count;
  g_capset.max_bdt_entries = pack->device_count;
  g_capset.max_irq_routes = total_routes;
  g_capset.max_dma_segments = 0;
  return JC_E_OK;
}

static jc_error_t jc_pal_z80_static_init(jc_pal_desc *out_desc) {
  jc_error_t err;
  jc_bdt_header_v1 *bdt = 0;
  jc_u16 routes = 0;
  if (!out_desc) {
    return JC_E_INTERNAL_ASSERT;
  }
  if (!JC_PAL_BOARD_PACK.board_id || !JC_PAL_BOARD_PACK.board_version) {
    return JC_E_DEV_UNSUPPORTED;
  }
  err = jc_pal_z80_build_bdt(&JC_PAL_BOARD_PACK, &bdt, &routes);
  if (err != JC_E_OK) {
    return err;
  }
  err = jc_pal_z80_build_capset(&JC_PAL_BOARD_PACK, bdt, routes);
  if (err != JC_E_OK) {
    return err;
  }

  out_desc->platform_id = JC_PAL_BOARD_PACK.board_id;
  out_desc->platform_version = JC_PAL_BOARD_PACK.board_version;
  out_desc->platform_caps = JC_PAL_BOARD_PACK.platform_caps;
  out_desc->platform_flags = JC_PAL_FLAG_NO_PROBE;
  out_desc->bdt = bdt;
  out_desc->capset = &g_capset;
  out_desc->console = JC_PAL_BOARD_PACK.console;
  out_desc->block = JC_PAL_BOARD_PACK.block;
  out_desc->timer = JC_PAL_BOARD_PACK.timer;
  out_desc->memmap = JC_PAL_BOARD_PACK.memmap;
  out_desc->keyboard = JC_PAL_BOARD_PACK.keyboard;
  out_desc->video = JC_PAL_BOARD_PACK.video;
  out_desc->rtc = JC_PAL_BOARD_PACK.rtc;
  out_desc->dma_sync = JC_PAL_BOARD_PACK.dma_sync;
  return JC_E_OK;
}

void jc_pal_z80_static_bind(void) { jc_pal_register(jc_pal_z80_static_init); }

static const jc_component_vtable g_pal_z80_vtable = {0, 0};

const jc_component_desc JC_COMPONENT_DESC = {
    JC_COMPONENT_ID_PAL_Z80_STATIC,
    1,
    0,
    1,
    0,
    0,
    &g_pal_z80_vtable,
    "pal_z80_static"};
