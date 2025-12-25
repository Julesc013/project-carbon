#include "pal_z80_board.h"

#include "jc_contracts_autogen.h"
#include "jc_fault.h"

#define S100_SECTOR_COUNT 32u

static jc_u8 g_s100_storage[S100_SECTOR_COUNT * 512u];
static jc_u64 g_s100_ticks;

static void s100_copy(jc_u8 *dst, const jc_u8 *src, jc_u32 len) {
  while (len--) {
    *dst++ = *src++;
  }
}

static jc_error_t s100_console_write(void *ctx,
                                     const char *data,
                                     jc_u32 len) {
  (void)ctx;
  (void)data;
  (void)len;
  return JC_E_OK;
}

static jc_error_t s100_console_read(void *ctx,
                                    char *out,
                                    jc_u32 len,
                                    jc_u32 *out_len) {
  (void)ctx;
  (void)out;
  (void)len;
  if (out_len) {
    *out_len = 0;
  }
  return JC_E_OK;
}

static jc_error_t s100_console_flush(void *ctx) {
  (void)ctx;
  return JC_E_OK;
}

static jc_error_t s100_block_read(void *ctx,
                                  jc_u32 lba,
                                  jc_u8 *buf,
                                  jc_u16 count512) {
  jc_u32 i;
  jc_u32 offset;
  (void)ctx;
  if (jc_fault_consume(JC_FAULT_IO_TIMEOUT)) {
    return JC_E_DEV_IO_TIMEOUT;
  }
  if (jc_fault_consume(JC_FAULT_BAD_SECTOR)) {
    return JC_E_DEV_IO_ERROR;
  }
  if (!buf) {
    return JC_E_INTERNAL_ASSERT;
  }
  if ((jc_u32)lba + (jc_u32)count512 > S100_SECTOR_COUNT) {
    return JC_E_DEV_IO_ERROR;
  }
  if (jc_fault_consume(JC_FAULT_PARTIAL_READ)) {
    if (count512 > 0u) {
      offset = lba * 512u;
      s100_copy(buf, &g_s100_storage[offset], 512u);
    }
    return JC_E_DEV_IO_ERROR;
  }
  for (i = 0; i < count512; ++i) {
    offset = (lba + i) * 512u;
    s100_copy(buf + i * 512u, &g_s100_storage[offset], 512u);
  }
  return JC_E_OK;
}

static jc_error_t s100_block_write(void *ctx,
                                   jc_u32 lba,
                                   const jc_u8 *buf,
                                   jc_u16 count512) {
  jc_u32 i;
  jc_u32 offset;
  (void)ctx;
  if (jc_fault_consume(JC_FAULT_IO_TIMEOUT)) {
    return JC_E_DEV_IO_TIMEOUT;
  }
  if (jc_fault_consume(JC_FAULT_BAD_SECTOR)) {
    return JC_E_DEV_IO_ERROR;
  }
  if (!buf) {
    return JC_E_INTERNAL_ASSERT;
  }
  if ((jc_u32)lba + (jc_u32)count512 > S100_SECTOR_COUNT) {
    return JC_E_DEV_IO_ERROR;
  }
  if (jc_fault_consume(JC_FAULT_PARTIAL_READ)) {
    if (count512 > 0u) {
      offset = lba * 512u;
      s100_copy(&g_s100_storage[offset], buf, 512u);
    }
    return JC_E_DEV_IO_ERROR;
  }
  for (i = 0; i < count512; ++i) {
    offset = (lba + i) * 512u;
    s100_copy(&g_s100_storage[offset], buf + i * 512u, 512u);
  }
  return JC_E_OK;
}

static jc_error_t s100_block_get_params(void *ctx,
                                        jc_pal_block_params *out_params) {
  (void)ctx;
  if (!out_params) {
    return JC_E_INTERNAL_ASSERT;
  }
  out_params->block_size_bytes = 512u;
  out_params->max_sectors_per_op = 1u;
  out_params->total_sectors = S100_SECTOR_COUNT;
  out_params->timeout_ticks = 100u;
  return JC_E_OK;
}

static jc_u64 s100_timer_ticks(void *ctx) {
  (void)ctx;
  g_s100_ticks.lo++;
  if (g_s100_ticks.lo == 0u) {
    g_s100_ticks.hi++;
  }
  return g_s100_ticks;
}

static jc_u32 s100_timer_hz(void *ctx) {
  (void)ctx;
  return 100u;
}

static void s100_timer_sleep(void *ctx, jc_u32 ticks) {
  (void)ctx;
  g_s100_ticks.lo += ticks;
  if (g_s100_ticks.lo < ticks) {
    g_s100_ticks.hi++;
  }
}

typedef struct {
  jc_mem_region_header_v1 header;
  jc_mem_region_entry_v1 entries[2];
} s100_mem_table;

static const s100_mem_table g_s100_mem = {
    {JC_MAGIC_MEM_REGION_HEADER,
     1,
     (jc_u16)sizeof(jc_mem_region_header_v1),
     (jc_u16)sizeof(jc_mem_region_entry_v1),
     2,
     (jc_u32)sizeof(s100_mem_table)},
    {{JC_MEM_REGION_KIND_RAM,
      JC_MEM_ATTR_CACHEABLE_MASK,
      0,
      {0x00000000u, 0u},
      {0x00020000u, 0u},
      0},
     {JC_MEM_REGION_KIND_ROM,
      JC_MEM_ATTR_CACHEABLE_MASK,
      0,
      {0x00020000u, 0u},
      {0x00008000u, 0u},
      0}}};

static const jc_mem_region_header_v1 *s100_memmap_get(void *ctx) {
  (void)ctx;
  return &g_s100_mem.header;
}

static const jc_pal_console_vtable g_s100_console_vtable = {
    s100_console_write, s100_console_read, s100_console_flush};
static const jc_pal_block_vtable g_s100_block_vtable = {
    s100_block_read, s100_block_write, s100_block_get_params};
static const jc_pal_timer_vtable g_s100_timer_vtable = {s100_timer_ticks,
                                                        s100_timer_hz,
                                                        s100_timer_sleep};
static const jc_pal_memmap_vtable g_s100_memmap_vtable = {s100_memmap_get};

static const jc_pal_board_device g_s100_devices[] = {
    {JC_DEVCLASS_UART,
     0,
     0,
     1,
     JC_DEV_COMPAT_POLLING_MASK | JC_DEV_COMPAT_PORT_IO_MASK,
     0,
     {0u, 0u},
     0u,
     0x10u,
     2u,
     0u,
     0u,
     0u,
     0u,
     0,
     0,
     {0u, 0u},
     0u,
     0u},
    {JC_DEVCLASS_TIMER,
     0,
     0,
     1,
     JC_DEV_COMPAT_POLLING_MASK | JC_DEV_COMPAT_PORT_IO_MASK,
     0,
     {0u, 0u},
     0u,
     0x20u,
     2u,
     0u,
     0u,
     0u,
     0u,
     0,
     0,
     {0u, 0u},
     0u,
     0u},
    {JC_DEVCLASS_PIC,
     0,
     0,
     1,
     JC_DEV_COMPAT_POLLING_MASK | JC_DEV_COMPAT_PORT_IO_MASK,
     0,
     {0u, 0u},
     0u,
     0x30u,
     2u,
     0u,
     0u,
     0u,
     0u,
     0,
     0,
     {0u, 0u},
     0u,
     0u},
    {JC_DEVCLASS_STORAGE,
     0,
     0,
     1,
     JC_DEV_COMPAT_POLLING_MASK | JC_DEV_COMPAT_PORT_IO_MASK,
     0,
     {0u, 0u},
     0u,
     0x40u,
     8u,
     512u,
     0u,
     0u,
     0u,
     0,
     0,
     {0u, 0u},
     0u,
     0u},
};

const jc_pal_board_pack JC_PAL_BOARD_PACK = {
    "s100_ref",
    "s100-ref-v1",
    0,
    0,
    2,
    0,
    0,
    {0, 0, 0},
    JC_CAP_HAS_IRQ,
    JC_PAL_BOOT_SERIAL | JC_PAL_BOOT_DISK,
    g_s100_devices,
    (jc_u16)(sizeof(g_s100_devices) / sizeof(g_s100_devices[0])),
    0,
    &g_s100_mem.header,
    {&g_s100_console_vtable, 0},
    {&g_s100_block_vtable, 0},
    {&g_s100_timer_vtable, 0},
    {&g_s100_memmap_vtable, 0},
    {0, 0},
    {0, 0},
    {0, 0},
    {0, 0}};
