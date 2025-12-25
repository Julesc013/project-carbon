#include "jc_dos_util.h"

#include "jc_config.h"
#include "jc_fastmem.h"

jc_u32 jc_dos_strlen(const char *s) {
  jc_u32 len = 0;
  while (s && s[len] != '\0') {
    len++;
  }
  return len;
}

int jc_dos_strcmp(const char *a, const char *b) {
  jc_u32 i = 0;
  if (a == b) {
    return 0;
  }
  if (!a) {
    return -1;
  }
  if (!b) {
    return 1;
  }
  while (a[i] && b[i]) {
    if (a[i] != b[i]) {
      return (a[i] < b[i]) ? -1 : 1;
    }
    i++;
  }
  if (a[i] == b[i]) {
    return 0;
  }
  return a[i] ? 1 : -1;
}

int jc_dos_strncmp(const char *a, const char *b, jc_u32 n) {
  jc_u32 i = 0;
  if (n == 0) {
    return 0;
  }
  if (a == b) {
    return 0;
  }
  if (!a) {
    return -1;
  }
  if (!b) {
    return 1;
  }
  while (i < n && a[i] && b[i]) {
    if (a[i] != b[i]) {
      return (a[i] < b[i]) ? -1 : 1;
    }
    i++;
  }
  if (i == n) {
    return 0;
  }
  if (a[i] == b[i]) {
    return 0;
  }
  return a[i] ? 1 : -1;
}

static char jc_dos_to_upper(char c) {
  if (c >= 'a' && c <= 'z') {
    return (char)(c - 'a' + 'A');
  }
  return c;
}

int jc_dos_strcasecmp(const char *a, const char *b) {
  jc_u32 i = 0;
  if (a == b) {
    return 0;
  }
  if (!a) {
    return -1;
  }
  if (!b) {
    return 1;
  }
  while (a[i] && b[i]) {
    char ca = jc_dos_to_upper(a[i]);
    char cb = jc_dos_to_upper(b[i]);
    if (ca != cb) {
      return (ca < cb) ? -1 : 1;
    }
    i++;
  }
  if (a[i] == b[i]) {
    return 0;
  }
  return a[i] ? 1 : -1;
}

int jc_dos_is_space(char c) {
  return c == ' ' || c == '\t' || c == '\r' || c == '\n';
}

static int jc_dos_hex_val(char c, jc_u32 *out) {
  if (c >= '0' && c <= '9') {
    *out = (jc_u32)(c - '0');
    return 1;
  }
  if (c >= 'a' && c <= 'f') {
    *out = (jc_u32)(c - 'a' + 10);
    return 1;
  }
  if (c >= 'A' && c <= 'F') {
    *out = (jc_u32)(c - 'A' + 10);
    return 1;
  }
  return 0;
}

int jc_dos_parse_u32(const char *s, jc_u32 *out) {
  jc_u32 value = 0;
  jc_u32 digit = 0;
  jc_u32 i = 0;
  int saw_digit = 0;

  if (!s || !out) {
    return 0;
  }
  while (jc_dos_is_space(s[i])) {
    i++;
  }
  if (s[i] == '0' && (s[i + 1] == 'x' || s[i + 1] == 'X')) {
    i += 2;
    while (jc_dos_hex_val(s[i], &digit)) {
      value = (value << 4) | digit;
      i++;
      saw_digit = 1;
    }
  } else {
    while (s[i] >= '0' && s[i] <= '9') {
      value = value * 10u + (jc_u32)(s[i] - '0');
      i++;
      saw_digit = 1;
    }
    if (!saw_digit) {
      while (jc_dos_hex_val(s[i], &digit)) {
        value = (value << 4) | digit;
        i++;
        saw_digit = 1;
      }
    }
  }
  if (!saw_digit) {
    return 0;
  }
  *out = value;
  return 1;
}

void jc_dos_memcpy(void *dst, const void *src, jc_u32 len) {
#if JC_CFG_ENABLE_FASTMEM
  if (jc_fastmem_is_enabled()) {
    jc_fastmem_memcpy(dst, src, len);
    return;
  }
#endif
  {
    jc_u32 i;
    jc_u8 *d = (jc_u8 *)dst;
    const jc_u8 *s = (const jc_u8 *)src;
    if (!d || !s) {
      return;
    }
    for (i = 0; i < len; ++i) {
      d[i] = s[i];
    }
  }
}

void jc_dos_memset(void *dst, jc_u8 value, jc_u32 len) {
#if JC_CFG_ENABLE_FASTMEM
  if (jc_fastmem_is_enabled()) {
    jc_fastmem_memset(dst, value, len);
    return;
  }
#endif
  {
    jc_u32 i;
    jc_u8 *d = (jc_u8 *)dst;
    if (!d) {
      return;
    }
    for (i = 0; i < len; ++i) {
      d[i] = value;
    }
  }
}

void jc_dos_memmove(void *dst, const void *src, jc_u32 len) {
#if JC_CFG_ENABLE_FASTMEM
  if (jc_fastmem_is_enabled()) {
    jc_fastmem_memmove(dst, src, len);
    return;
  }
#endif
  {
    jc_u8 *d = (jc_u8 *)dst;
    const jc_u8 *s = (const jc_u8 *)src;
    if (!d || !s || len == 0u || d == s) {
      return;
    }
    if (d < s || d >= (s + len)) {
      jc_dos_memcpy(dst, src, len);
      return;
    }
    while (len > 0u) {
      len--;
      d[len] = s[len];
    }
  }
}

int jc_dos_memcmp(const void *a, const void *b, jc_u32 len) {
  jc_u32 i;
  const jc_u8 *pa = (const jc_u8 *)a;
  const jc_u8 *pb = (const jc_u8 *)b;
  if (pa == pb || len == 0) {
    return 0;
  }
  if (!pa) {
    return -1;
  }
  if (!pb) {
    return 1;
  }
  for (i = 0; i < len; ++i) {
    if (pa[i] != pb[i]) {
      return (pa[i] < pb[i]) ? -1 : 1;
    }
  }
  return 0;
}

void jc_dos_u32_to_hex(char out[8], jc_u32 value) {
  int i;
  for (i = 7; i >= 0; --i) {
    jc_u32 nib = value & 0xFu;
    if (nib < 10u) {
      out[i] = (char)('0' + nib);
    } else {
      out[i] = (char)('A' + (nib - 10u));
    }
    value >>= 4;
  }
}

void jc_dos_u16_to_hex(char out[4], jc_u16 value) {
  int i;
  for (i = 3; i >= 0; --i) {
    jc_u16 nib = (jc_u16)(value & 0xFu);
    if (nib < 10u) {
      out[i] = (char)('0' + nib);
    } else {
      out[i] = (char)('A' + (nib - 10u));
    }
    value >>= 4;
  }
}

jc_u32 jc_dos_crc32_init(void) {
  return 0xFFFFFFFFu;
}

jc_u32 jc_dos_crc32_update(jc_u32 crc, const jc_u8 *data, jc_u32 len) {
  jc_u32 i;
  jc_u32 j;
  for (i = 0; i < len; ++i) {
    jc_u32 byte = (jc_u32)data[i];
    crc ^= byte;
    for (j = 0; j < 8; ++j) {
      jc_u32 mask = (crc & 1u) ? 0xEDB88320u : 0u;
      crc = (crc >> 1) ^ mask;
    }
  }
  return crc;
}

jc_u32 jc_dos_crc32_finalize(jc_u32 crc) {
  return crc ^ 0xFFFFFFFFu;
}

jc_u32 jc_dos_crc32(const jc_u8 *data, jc_u32 len) {
  return jc_dos_crc32_finalize(jc_dos_crc32_update(jc_dos_crc32_init(),
                                                  data, len));
}
