#ifndef JC_PAL_H
#define JC_PAL_H

#include "jc_caps.h"
#include "jc_contracts.h"
#include "jc_error.h"
#include "jc_types.h"

#define JC_PAL_ABI_MAJOR 1u
#define JC_PAL_ABI_MINOR 0u

#define JC_PAL_FLAG_DETERMINISTIC (1u << 0)
#define JC_PAL_FLAG_NO_PROBE (1u << 1)
#define JC_PAL_FLAG_ROM_BOOT (1u << 2)

#define JC_PAL_DMA_SYNC_TO_DEVICE (1u << 0)
#define JC_PAL_DMA_SYNC_TO_CPU (1u << 1)

#define JC_PAL_VIDEO_FMT_TEXT 0u
#define JC_PAL_VIDEO_FMT_INDEXED8 1u
#define JC_PAL_VIDEO_FMT_RGB565 2u

typedef struct {
  jc_u32 block_size_bytes;
  jc_u32 max_sectors_per_op;
  jc_u32 total_sectors;
  jc_u32 timeout_ticks;
} jc_pal_block_params;

typedef struct {
  jc_u16 keycode;
  jc_u16 modifiers;
} jc_pal_key_event;

typedef struct {
  jc_u16 width;
  jc_u16 height;
  jc_u16 pitch_bytes;
  jc_u16 format;
  jc_u64 framebuffer_ptr;
} jc_pal_video_info;

typedef struct {
  jc_u16 year;
  jc_u8 month;
  jc_u8 day;
  jc_u8 hour;
  jc_u8 minute;
  jc_u8 second;
  jc_u8 reserved0;
} jc_pal_rtc_time;

typedef struct {
  jc_error_t (*write)(void *ctx, const char *data, jc_u32 len);
  jc_error_t (*read)(void *ctx, char *out, jc_u32 len, jc_u32 *out_len);
  jc_error_t (*flush)(void *ctx);
} jc_pal_console_vtable;

typedef struct {
  jc_error_t (*read)(void *ctx, jc_u32 lba, jc_u8 *buf, jc_u16 count512);
  jc_error_t (*write)(void *ctx,
                      jc_u32 lba,
                      const jc_u8 *buf,
                      jc_u16 count512);
  jc_error_t (*get_params)(void *ctx, jc_pal_block_params *out_params);
} jc_pal_block_vtable;

typedef struct {
  jc_u64 (*ticks)(void *ctx);
  jc_u32 (*tick_hz)(void *ctx);
  void (*sleep_ticks)(void *ctx, jc_u32 ticks);
} jc_pal_timer_vtable;

typedef struct {
  const jc_mem_region_header_v1 *(*get_table)(void *ctx);
} jc_pal_memmap_vtable;

typedef struct {
  jc_error_t (*read)(void *ctx, jc_pal_key_event *out_event);
  int (*poll)(void *ctx, jc_pal_key_event *out_event);
} jc_pal_keyboard_vtable;

typedef struct {
  jc_error_t (*get_info)(void *ctx, jc_pal_video_info *out_info);
  jc_error_t (*set_mode)(void *ctx, jc_u16 mode_id);
  jc_error_t (*present)(void *ctx);
} jc_pal_video_vtable;

typedef struct {
  jc_error_t (*get_time)(void *ctx, jc_pal_rtc_time *out_time);
} jc_pal_rtc_vtable;

typedef struct {
  jc_error_t (*sync)(void *ctx, jc_u64 addr, jc_u32 size, jc_u32 flags);
} jc_pal_dma_sync_vtable;

typedef struct {
  const jc_pal_console_vtable *vtable;
  void *ctx;
} jc_pal_console;

typedef struct {
  const jc_pal_block_vtable *vtable;
  void *ctx;
} jc_pal_block;

typedef struct {
  const jc_pal_timer_vtable *vtable;
  void *ctx;
} jc_pal_timer;

typedef struct {
  const jc_pal_memmap_vtable *vtable;
  void *ctx;
} jc_pal_memmap;

typedef struct {
  const jc_pal_keyboard_vtable *vtable;
  void *ctx;
} jc_pal_keyboard;

typedef struct {
  const jc_pal_video_vtable *vtable;
  void *ctx;
} jc_pal_video;

typedef struct {
  const jc_pal_rtc_vtable *vtable;
  void *ctx;
} jc_pal_rtc;

typedef struct {
  const jc_pal_dma_sync_vtable *vtable;
  void *ctx;
} jc_pal_dma_sync;

typedef struct {
  jc_u32 abi_major;
  jc_u32 abi_minor;
  const char *platform_id;
  const char *platform_version;
  jc_u32 platform_caps;
  jc_u32 platform_flags;
  const jc_bdt_header_v1 *bdt;
  const jc_capset_v1 *capset;
  jc_pal_console console;
  jc_pal_block block;
  jc_pal_timer timer;
  jc_pal_memmap memmap;
  jc_pal_keyboard keyboard;
  jc_pal_video video;
  jc_pal_rtc rtc;
  jc_pal_dma_sync dma_sync;
} jc_pal_desc;

typedef jc_error_t (*jc_pal_init_fn)(jc_pal_desc *out_desc);

void jc_pal_register(jc_pal_init_fn init_fn);
jc_error_t jc_pal_init(jc_pal_desc *out_desc);
jc_error_t jc_pal_validate(const jc_pal_desc *desc);

#endif /* JC_PAL_H */
