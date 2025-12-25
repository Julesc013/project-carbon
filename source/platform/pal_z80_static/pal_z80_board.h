#ifndef PAL_Z80_BOARD_H
#define PAL_Z80_BOARD_H

#include "jc_caps.h"
#include "jc_contracts.h"
#include "jc_error.h"
#include "jc_pal.h"
#include "jc_types.h"

#define JC_PAL_BOOT_SERIAL (1u << 0)
#define JC_PAL_BOOT_DISK (1u << 1)
#define JC_PAL_BOOT_ROMWBW (1u << 2)

typedef struct {
  jc_u16 class_id;
  jc_u16 subclass_id;
  jc_u16 instance_id;
  jc_u16 device_version;
  jc_u32 caps0;
  jc_u32 caps1;
  jc_u64 mmio_base;
  jc_u32 mmio_size;
  jc_u32 io_port_base;
  jc_u16 io_port_size;
  jc_u16 block_sector_size;
  jc_u16 cai_queue_count;
  jc_u16 cai_doorbell_offset;
  const jc_bdt_irq_route_v1 *irq_routes;
  jc_u16 irq_route_count;
  jc_u64 aux_ptr;
  jc_u32 aux_size;
  jc_u16 aux_type;
} jc_pal_board_device;

typedef struct {
  const char *board_id;
  const char *board_version;
  jc_u8 cpu_ladder_id;
  jc_u8 fpu_ladder_id;
  jc_u8 presented_cpu_tier;
  jc_u8 presented_fpu_tier;
  jc_u8 profile_id;
  jc_u8 reserved0[3];
  jc_u32 platform_caps;
  jc_u32 boot_methods;
  const jc_pal_board_device *devices;
  jc_u16 device_count;
  jc_u16 reserved1;
  const jc_mem_region_header_v1 *mem_regions;
  jc_pal_console console;
  jc_pal_block block;
  jc_pal_timer timer;
  jc_pal_memmap memmap;
  jc_pal_keyboard keyboard;
  jc_pal_video video;
  jc_pal_rtc rtc;
  jc_pal_dma_sync dma_sync;
} jc_pal_board_pack;

extern const jc_pal_board_pack JC_PAL_BOARD_PACK;

#endif /* PAL_Z80_BOARD_H */
