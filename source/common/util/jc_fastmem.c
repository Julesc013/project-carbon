#include "jc_fastmem.h"

#include "jc_config.h"

static jc_u32 g_fastmem_caps;
static int g_fastmem_enabled;

void jc_fastmem_init(jc_u32 caps) {
  g_fastmem_caps = caps;
  g_fastmem_enabled = (JC_CFG_ENABLE_FASTMEM != 0);
}

void jc_fastmem_set_enabled(int enable) {
  g_fastmem_enabled = enable ? 1 : 0;
}

int jc_fastmem_is_enabled(void) {
  return g_fastmem_enabled;
}

jc_u32 jc_fastmem_caps(void) {
  return g_fastmem_caps;
}

static int jc_fastmem_can_wide(const void *dst, const void *src) {
  unsigned long d = (unsigned long)dst;
  unsigned long s = (unsigned long)src;
  if ((g_fastmem_caps & JC_FASTMEM_CAP_WIDE_MOVES) == 0u) {
    return 0;
  }
  return ((d | s) & 3u) == 0u;
}

void jc_fastmem_memcpy(void *dst, const void *src, jc_u32 len) {
  jc_u32 i;
  jc_u8 *d8 = (jc_u8 *)dst;
  const jc_u8 *s8 = (const jc_u8 *)src;
  if (!d8 || !s8 || len == 0u) {
    return;
  }
  if (jc_fastmem_can_wide(dst, src) && len >= 4u) {
    jc_u32 count = len / 4u;
    jc_u32 rem = len % 4u;
    jc_u32 *d32 = (jc_u32 *)dst;
    const jc_u32 *s32 = (const jc_u32 *)src;
    for (i = 0; i < count; ++i) {
      d32[i] = s32[i];
    }
    d8 = (jc_u8 *)(d32 + count);
    s8 = (const jc_u8 *)(s32 + count);
    for (i = 0; i < rem; ++i) {
      d8[i] = s8[i];
    }
    return;
  }
  for (i = 0; i < len; ++i) {
    d8[i] = s8[i];
  }
}

void jc_fastmem_memset(void *dst, jc_u8 value, jc_u32 len) {
  jc_u32 i;
  jc_u8 *d8 = (jc_u8 *)dst;
  if (!d8 || len == 0u) {
    return;
  }
  if ((g_fastmem_caps & JC_FASTMEM_CAP_WIDE_MOVES) != 0u &&
      (((unsigned long)dst) & 3u) == 0u && len >= 4u) {
    jc_u32 count = len / 4u;
    jc_u32 rem = len % 4u;
    jc_u32 word = (jc_u32)value;
    jc_u32 *d32 = (jc_u32 *)dst;
    word |= word << 8;
    word |= word << 16;
    for (i = 0; i < count; ++i) {
      d32[i] = word;
    }
    d8 = (jc_u8 *)(d32 + count);
    for (i = 0; i < rem; ++i) {
      d8[i] = value;
    }
    return;
  }
  for (i = 0; i < len; ++i) {
    d8[i] = value;
  }
}

void jc_fastmem_memmove(void *dst, const void *src, jc_u32 len) {
  jc_u8 *d8 = (jc_u8 *)dst;
  const jc_u8 *s8 = (const jc_u8 *)src;
  if (!d8 || !s8 || len == 0u || d8 == s8) {
    return;
  }
  if (d8 < s8 || d8 >= (s8 + len)) {
    jc_fastmem_memcpy(dst, src, len);
    return;
  }
  if (jc_fastmem_can_wide(dst, src) && len >= 4u) {
    jc_u32 count = len / 4u;
    jc_u32 rem = len % 4u;
    jc_u32 *d32 = (jc_u32 *)dst;
    const jc_u32 *s32 = (const jc_u32 *)src;
    jc_u32 idx = count;
    while (idx > 0u) {
      idx--;
      d32[idx] = s32[idx];
    }
    if (rem > 0u) {
      jc_u32 i;
      d8 = (jc_u8 *)(d32 + count);
      s8 = (const jc_u8 *)(s32 + count);
      for (i = rem; i > 0u; --i) {
        d8[i - 1u] = s8[i - 1u];
      }
    }
    return;
  }
  while (len > 0u) {
    len--;
    d8[len] = s8[len];
  }
}
