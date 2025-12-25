#include "jc_block_robust.h"

#include "jc_block.h"
#include "jc_timer.h"

typedef struct {
  jc_u32 lba;
  jc_error_t err;
  int in_use;
} jc_bad_sector_entry;

static jc_bad_sector_entry g_bad_sectors[JC_BLOCK_BAD_SECTOR_MAX];
static jc_u32 g_bad_sector_next;
static jc_u32 g_inject_fail_count;
static jc_error_t g_inject_fail_err;

static void jc_block_backoff_wait(jc_u32 attempt) {
  jc_u32 ticks = JC_BLOCK_RETRY_BACKOFF_TICKS;
  jc_u32 i;
  for (i = 0; i < attempt; ++i) {
    if (ticks > 0xFFFFFFFFu / 2u) {
      break;
    }
    ticks <<= 1;
  }
  if (ticks == 0u) {
    return;
  }
  {
    jc_u64 deadline = jc_timer_deadline_from_now(ticks);
    while (!jc_timer_expired(deadline)) {
    }
  }
}

static int jc_block_is_bad(jc_u32 lba, jc_error_t *out_err) {
  jc_u32 i;
  for (i = 0; i < JC_BLOCK_BAD_SECTOR_MAX; ++i) {
    if (g_bad_sectors[i].in_use && g_bad_sectors[i].lba == lba) {
      if (out_err) {
        *out_err = g_bad_sectors[i].err;
      }
      return 1;
    }
  }
  return 0;
}

static void jc_block_mark_bad(jc_u32 lba, jc_error_t err) {
  jc_u32 slot = g_bad_sector_next % JC_BLOCK_BAD_SECTOR_MAX;
  g_bad_sectors[slot].lba = lba;
  g_bad_sectors[slot].err = err;
  g_bad_sectors[slot].in_use = 1;
  g_bad_sector_next = (g_bad_sector_next + 1u) % JC_BLOCK_BAD_SECTOR_MAX;
}

static void jc_block_mark_bad_range(jc_u32 lba,
                                    jc_u16 count512,
                                    jc_error_t err) {
  jc_u16 i;
  for (i = 0; i < count512; ++i) {
    jc_block_mark_bad(lba + (jc_u32)i, err);
  }
}

static jc_error_t jc_block_inject_fail(void) {
  if (g_inject_fail_count == 0u) {
    return JC_E_OK;
  }
  g_inject_fail_count--;
  return g_inject_fail_err;
}

jc_error_t jc_blk_read_robust(jc_u32 lba, jc_u8 *buf, jc_u16 count512) {
  jc_error_t err;
  jc_u32 attempt;
  if (!buf || count512 == 0u) {
    return JC_E_INTERNAL_ASSERT;
  }
  for (attempt = 0; attempt < count512; ++attempt) {
    jc_error_t bad_err = JC_E_OK;
    if (jc_block_is_bad(lba + attempt, &bad_err)) {
      return bad_err;
    }
  }
  for (attempt = 0; attempt <= JC_BLOCK_RETRY_MAX; ++attempt) {
    err = jc_block_inject_fail();
    if (err == JC_E_OK) {
      err = jc_blk_read(lba, buf, count512);
    }
    if (err == JC_E_OK) {
      return JC_E_OK;
    }
    if (err != JC_E_DEV_IO_TIMEOUT || attempt >= JC_BLOCK_RETRY_MAX) {
      break;
    }
    jc_block_backoff_wait(attempt);
  }
  if (err == JC_E_DEV_IO_TIMEOUT || err == JC_E_DEV_IO_ERROR) {
    jc_block_mark_bad_range(lba, count512, err);
  }
  return err;
}

jc_error_t jc_blk_write_robust(jc_u32 lba,
                               const jc_u8 *buf,
                               jc_u16 count512) {
  jc_error_t err;
  jc_u32 attempt;
  if (!buf || count512 == 0u) {
    return JC_E_INTERNAL_ASSERT;
  }
  for (attempt = 0; attempt < count512; ++attempt) {
    jc_error_t bad_err = JC_E_OK;
    if (jc_block_is_bad(lba + attempt, &bad_err)) {
      return bad_err;
    }
  }
  for (attempt = 0; attempt <= JC_BLOCK_RETRY_MAX; ++attempt) {
    err = jc_block_inject_fail();
    if (err == JC_E_OK) {
      err = jc_blk_write(lba, buf, count512);
    }
    if (err == JC_E_OK) {
      return JC_E_OK;
    }
    if (err != JC_E_DEV_IO_TIMEOUT || attempt >= JC_BLOCK_RETRY_MAX) {
      break;
    }
    jc_block_backoff_wait(attempt);
  }
  if (err == JC_E_DEV_IO_TIMEOUT || err == JC_E_DEV_IO_ERROR) {
    jc_block_mark_bad_range(lba, count512, err);
  }
  return err;
}

void jc_blk_robust_inject_fail(jc_u32 fail_count, jc_error_t err) {
  g_inject_fail_count = fail_count;
  g_inject_fail_err = err;
}

void jc_blk_robust_clear_bad_sectors(void) {
  jc_u32 i;
  for (i = 0; i < JC_BLOCK_BAD_SECTOR_MAX; ++i) {
    g_bad_sectors[i].in_use = 0;
    g_bad_sectors[i].lba = 0u;
    g_bad_sectors[i].err = JC_E_OK;
  }
  g_bad_sector_next = 0;
}
