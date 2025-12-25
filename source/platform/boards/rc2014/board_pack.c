#include "pal_z80_board.h"

#include "jc_contracts_autogen.h"
#include "jc_fault.h"

#define RC2014_SECTOR_COUNT 16u

static jc_u8 g_rc2014_storage[RC2014_SECTOR_COUNT * 512u];
static jc_u64 g_rc2014_ticks;

static void rc2014_copy(jc_u8 *dst, const jc_u8 *src, jc_u32 len) {
  while (len--) {
    *dst++ = *src++;
  }
}

static jc_error_t rc2014_console_write(void *ctx,
                                       const char *data,
                                       jc_u32 len) {
  (void)ctx;
  (void)data;
  (void)len;
  return JC_E_OK;
}

static jc_error_t rc2014_console_read(void *ctx,
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

static jc_error_t rc2014_console_flush(void *ctx) {
  (void)ctx;
  return JC_E_OK;
}

static jc_error_t rc2014_block_read(void *ctx,
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
  if ((jc_u32)lba + (jc_u32)count512 > RC2014_SECTOR_COUNT) {
    return JC_E_DEV_IO_ERROR;
  }
  if (jc_fault_consume(JC_FAULT_PARTIAL_READ)) {
    if (count512 > 0u) {
      offset = lba * 512u;
      rc2014_copy(buf, &g_rc2014_storage[offset], 512u);
    }
    return JC_E_DEV_IO_ERROR;
  }
  for (i = 0; i < count512; ++i) {
    offset = (lba + i) * 512u;
    rc2014_copy(buf + i * 512u, &g_rc2014_storage[offset], 512u);
  }
  return JC_E_OK;
}

static jc_error_t rc2014_block_write(void *ctx,
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
  if ((jc_u32)lba + (jc_u32)count512 > RC2014_SECTOR_COUNT) {
    return JC_E_DEV_IO_ERROR;
  }
  if (jc_fault_consume(JC_FAULT_PARTIAL_READ)) {
    if (count512 > 0u) {
      offset = lba * 512u;
      rc2014_copy(&g_rc2014_storage[offset], buf, 512u);
    }
    return JC_E_DEV_IO_ERROR;
  }
  for (i = 0; i < count512; ++i) {
    offset = (lba + i) * 512u;
    rc2014_copy(&g_rc2014_storage[offset], buf + i * 512u, 512u);
  }
  return JC_E_OK;
}

static jc_error_t rc2014_block_get_params(void *ctx,
                                          jc_pal_block_params *out_params) {
  (void)ctx;
  if (!out_params) {
    return JC_E_INTERNAL_ASSERT;
  }
  out_params->block_size_bytes = 512u;
  out_params->max_sectors_per_op = 1u;
  out_params->total_sectors = RC2014_SECTOR_COUNT;
  out_params->timeout_ticks = 100u;
  return JC_E_OK;
}

static jc_u64 rc2014_timer_ticks(void *ctx) {
  (void)ctx;
  g_rc2014_ticks.lo++;
  if (g_rc2014_ticks.lo == 0u) {
    g_rc2014_ticks.hi++;
  }
  return g_rc2014_ticks;
}

static jc_u32 rc2014_timer_hz(void *ctx) {
  (void)ctx;
  return 100u;
}

static void rc2014_timer_sleep(void *ctx, jc_u32 ticks) {
  (void)ctx;
  g_rc2014_ticks.lo += ticks;
  if (g_rc2014_ticks.lo < ticks) {
    g_rc2014_ticks.hi++;
  }
}

typedef struct {
  jc_mem_region_header_v1 header;
  jc_mem_region_entry_v1 entries[2];
} rc2014_mem_table;

static const rc2014_mem_table g_rc2014_mem = {
    {JC_MAGIC_MEM_REGION_HEADER,
     1,
     (jc_u16)sizeof(jc_mem_region_header_v1),
     (jc_u16)sizeof(jc_mem_region_entry_v1),
     2,
     (jc_u32)sizeof(rc2014_mem_table)},
    {{JC_MEM_REGION_KIND_RAM,
      JC_MEM_ATTR_CACHEABLE_MASK,
      0,
      {0x00000000u, 0u},
      {0x00010000u, 0u},
      0},
     {JC_MEM_REGION_KIND_ROM,
      JC_MEM_ATTR_CACHEABLE_MASK,
      0,
      {0x00010000u, 0u},
      {0x00008000u, 0u},
      0}}};

static const jc_mem_region_header_v1 *rc2014_memmap_get(void *ctx) {
  (void)ctx;
  return &g_rc2014_mem.header;
}

static const jc_pal_console_vtable g_rc2014_console_vtable = {
    rc2014_console_write, rc2014_console_read, rc2014_console_flush};
static const jc_pal_block_vtable g_rc2014_block_vtable = {
    rc2014_block_read, rc2014_block_write, rc2014_block_get_params};
static const jc_pal_timer_vtable g_rc2014_timer_vtable = {
    rc2014_timer_ticks, rc2014_timer_hz, rc2014_timer_sleep};
static const jc_pal_memmap_vtable g_rc2014_memmap_vtable = {rc2014_memmap_get};

static const jc_pal_board_device g_rc2014_devices[] = {
    {JC_DEVCLASS_UART,
     0,
     0,
     1,
     JC_DEV_COMPAT_POLLING_MASK | JC_DEV_COMPAT_PORT_IO_MASK,
     0,
     {0u, 0u},
     0u,
     0x80u,
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
     0x90u,
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
     0x10u,
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
    "rc2014",
    "rc2014-v1",
    0,
    0,
    2,
    0,
    0,
    {0, 0, 0},
    0u,
    JC_PAL_BOOT_SERIAL | JC_PAL_BOOT_DISK,
    g_rc2014_devices,
    (jc_u16)(sizeof(g_rc2014_devices) / sizeof(g_rc2014_devices[0])),
    0,
    &g_rc2014_mem.header,
    {&g_rc2014_console_vtable, 0},
    {&g_rc2014_block_vtable, 0},
    {&g_rc2014_timer_vtable, 0},
    {&g_rc2014_memmap_vtable, 0},
    {0, 0},
    {0, 0},
    {0, 0},
    {0, 0}};
