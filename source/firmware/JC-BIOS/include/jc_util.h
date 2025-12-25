#ifndef JC_UTIL_H
#define JC_UTIL_H

#include "jc_types.h"

jc_u32 jc_strlen(const char *s);
int jc_strcmp(const char *a, const char *b);
int jc_strncmp(const char *a, const char *b, jc_u32 n);
int jc_strcasecmp(const char *a, const char *b);
int jc_is_space(char c);
int jc_is_hex_digit(char c);
int jc_parse_u32(const char *s, jc_u32 *out);

void jc_memcpy(void *dst, const void *src, jc_u32 len);
void jc_memset(void *dst, jc_u8 value, jc_u32 len);
int jc_memcmp(const void *a, const void *b, jc_u32 len);

void jc_u32_to_hex(char out[8], jc_u32 value);
void jc_u16_to_hex(char out[4], jc_u16 value);

jc_u64 jc_u64_make(jc_u32 lo, jc_u32 hi);
int jc_u64_is_zero(jc_u64 value);
int jc_u64_cmp(jc_u64 a, jc_u64 b);
jc_u64 jc_u64_add_u32(jc_u64 a, jc_u32 b);

jc_u32 jc_crc32_init(void);
jc_u32 jc_crc32_update(jc_u32 crc, const jc_u8 *data, jc_u32 len);
jc_u32 jc_crc32_finalize(jc_u32 crc);
jc_u32 jc_crc32(const jc_u8 *data, jc_u32 len);

#endif /* JC_UTIL_H */
