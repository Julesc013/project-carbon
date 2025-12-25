#include "cache_blk.h"

#include "bios_services.h"
#include "jc_config.h"
#include "jc_dos_util.h"
#include "mem_arena.h"

#define JC_CACHE_LINE_COUNT 8u
#define JC_CACHE_LINE_SIZE 512u

typedef struct {
  jc_u32 lba;
  jc_u8 valid;
  jc_u8 reserved[3];
} jc_cache_line;

typedef struct {
  int enabled;
  jc_u32 line_count;
  jc_u32 next_evict;
  jc_cache_line *lines;
  jc_u8 *data;
} jc_cache_state;

static jc_cache_state g_cache;

static jc_u8 *jc_cache_line_data(jc_u32 index) {
  return g_cache.data + index * JC_CACHE_LINE_SIZE;
}

static jc_u32 jc_cache_find(jc_u32 lba) {
  jc_u32 i;
  if (!g_cache.lines) {
    return 0xFFFFFFFFu;
  }
  for (i = 0; i < g_cache.line_count; ++i) {
    if (g_cache.lines[i].valid && g_cache.lines[i].lba == lba) {
      return i;
    }
  }
  return 0xFFFFFFFFu;
}

static jc_u32 jc_cache_alloc_line(void) {
  jc_u32 idx = g_cache.next_evict;
  g_cache.next_evict = (g_cache.next_evict + 1u) % g_cache.line_count;
  return idx;
}

static jc_error_t jc_cache_fill_line(jc_u32 index, jc_u32 lba) {
  jc_error_t err;
  jc_u8 *dst = jc_cache_line_data(index);
  err = jc_bios_block_read(lba, dst, 1);
  if (err != JC_E_OK) {
    return err;
  }
  g_cache.lines[index].lba = lba;
  g_cache.lines[index].valid = 1;
  return JC_E_OK;
}

jc_error_t jc_cache_blk_init(void) {
  jc_dos_arena *arena;
  jc_u32 lines_bytes;
  jc_u32 data_bytes;

  if (g_cache.lines) {
    return JC_E_OK;
  }
  if (JC_CFG_ENABLE_CACHE == 0) {
    return JC_E_DEV_UNSUPPORTED;
  }

  arena = jc_dos_arena_kernel();
  g_cache.line_count = JC_CACHE_LINE_COUNT;
  g_cache.next_evict = 0;

  lines_bytes = g_cache.line_count * sizeof(jc_cache_line);
  data_bytes = g_cache.line_count * JC_CACHE_LINE_SIZE;

  g_cache.lines = (jc_cache_line *)jc_dos_arena_alloc(arena, lines_bytes, 4);
  g_cache.data = (jc_u8 *)jc_dos_arena_alloc(arena, data_bytes, 4);
  if (!g_cache.lines || !g_cache.data) {
    g_cache.lines = 0;
    g_cache.data = 0;
    return JC_E_INTERNAL_ASSERT;
  }

  jc_dos_memset(g_cache.lines, 0, lines_bytes);
  jc_dos_memset(g_cache.data, 0, data_bytes);
  g_cache.enabled = 1;
  return JC_E_OK;
}

void jc_cache_blk_enable(int enable) {
  if (JC_CFG_ENABLE_CACHE == 0) {
    g_cache.enabled = 0;
    return;
  }
  if (!g_cache.lines) {
    g_cache.enabled = 0;
    return;
  }
  g_cache.enabled = enable ? 1 : 0;
}

int jc_cache_blk_is_enabled(void) {
  return g_cache.enabled != 0 && g_cache.lines != 0;
}

void jc_cache_blk_reset(void) {
  jc_u32 lines_bytes;
  jc_u32 data_bytes;
  if (!g_cache.lines || !g_cache.data) {
    return;
  }
  lines_bytes = g_cache.line_count * sizeof(jc_cache_line);
  data_bytes = g_cache.line_count * JC_CACHE_LINE_SIZE;
  jc_dos_memset(g_cache.lines, 0, lines_bytes);
  jc_dos_memset(g_cache.data, 0, data_bytes);
  g_cache.next_evict = 0;
}

jc_error_t jc_cache_blk_read(jc_u32 lba, jc_u8 *buf, jc_u16 count512) {
  jc_u16 i;
  if (!buf || count512 == 0) {
    return JC_E_INTERNAL_ASSERT;
  }
  if (!jc_cache_blk_is_enabled()) {
    return jc_bios_block_read(lba, buf, count512);
  }

  for (i = 0; i < count512; ++i) {
    jc_u32 idx = jc_cache_find(lba + i);
    if (idx == 0xFFFFFFFFu) {
      jc_error_t err;
      idx = jc_cache_alloc_line();
      err = jc_cache_fill_line(idx, lba + i);
      if (err != JC_E_OK) {
        return err;
      }
    }
    jc_dos_memcpy(buf + (jc_u32)i * JC_CACHE_LINE_SIZE,
                  jc_cache_line_data(idx),
                  JC_CACHE_LINE_SIZE);
  }
  return JC_E_OK;
}

jc_error_t jc_cache_blk_write(jc_u32 lba, const jc_u8 *buf, jc_u16 count512) {
  jc_u16 i;
  if (!buf || count512 == 0) {
    return JC_E_INTERNAL_ASSERT;
  }

  for (i = 0; i < count512; ++i) {
    jc_error_t err = jc_bios_block_write(
        lba + i, buf + (jc_u32)i * JC_CACHE_LINE_SIZE, 1);
    if (err != JC_E_OK) {
      return err;
    }
    if (jc_cache_blk_is_enabled()) {
      jc_u32 idx = jc_cache_find(lba + i);
      if (idx == 0xFFFFFFFFu) {
        idx = jc_cache_alloc_line();
        g_cache.lines[idx].lba = lba + i;
        g_cache.lines[idx].valid = 1;
      }
      jc_dos_memcpy(jc_cache_line_data(idx),
                    buf + (jc_u32)i * JC_CACHE_LINE_SIZE,
                    JC_CACHE_LINE_SIZE);
    }
  }
  return JC_E_OK;
}

jc_u32 jc_cache_blk_state_crc(void) {
  jc_u32 crc = jc_dos_crc32_init();
  jc_u32 i;
  if (!g_cache.lines) {
    return 0;
  }
  crc = jc_dos_crc32_update(crc, (const jc_u8 *)&g_cache.line_count,
                            sizeof(g_cache.line_count));
  crc = jc_dos_crc32_update(crc, (const jc_u8 *)&g_cache.next_evict,
                            sizeof(g_cache.next_evict));
  for (i = 0; i < g_cache.line_count; ++i) {
    crc = jc_dos_crc32_update(crc, (const jc_u8 *)&g_cache.lines[i].valid, 1);
    crc = jc_dos_crc32_update(crc, (const jc_u8 *)&g_cache.lines[i].lba,
                              sizeof(g_cache.lines[i].lba));
  }
  return jc_dos_crc32_finalize(crc);
}
