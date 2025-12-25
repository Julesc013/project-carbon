#ifndef JC_DOS_UTIL_H
#define JC_DOS_UTIL_H

#include "jc_types.h"

jc_u32 jc_dos_strlen(const char *s);
int jc_dos_strcmp(const char *a, const char *b);
int jc_dos_strncmp(const char *a, const char *b, jc_u32 n);
int jc_dos_strcasecmp(const char *a, const char *b);
int jc_dos_is_space(char c);
int jc_dos_parse_u32(const char *s, jc_u32 *out);

void jc_dos_memcpy(void *dst, const void *src, jc_u32 len);
void jc_dos_memset(void *dst, jc_u8 value, jc_u32 len);
void jc_dos_memmove(void *dst, const void *src, jc_u32 len);
int jc_dos_memcmp(const void *a, const void *b, jc_u32 len);

void jc_dos_u32_to_hex(char out[8], jc_u32 value);
void jc_dos_u16_to_hex(char out[4], jc_u16 value);

jc_u32 jc_dos_crc32_init(void);
jc_u32 jc_dos_crc32_update(jc_u32 crc, const jc_u8 *data, jc_u32 len);
jc_u32 jc_dos_crc32_finalize(jc_u32 crc);
jc_u32 jc_dos_crc32(const jc_u8 *data, jc_u32 len);

#endif /* JC_DOS_UTIL_H */
