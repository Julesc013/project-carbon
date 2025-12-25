#ifndef JC_FASTMEM_H
#define JC_FASTMEM_H

#include "jc_types.h"

#define JC_FASTMEM_CAP_WIDE_MOVES 0x00000001u

void jc_fastmem_init(jc_u32 caps);
void jc_fastmem_set_enabled(int enable);
int jc_fastmem_is_enabled(void);
jc_u32 jc_fastmem_caps(void);

void jc_fastmem_memcpy(void *dst, const void *src, jc_u32 len);
void jc_fastmem_memset(void *dst, jc_u8 value, jc_u32 len);
void jc_fastmem_memmove(void *dst, const void *src, jc_u32 len);

#endif /* JC_FASTMEM_H */
