#ifndef JC_TYPES_H
#define JC_TYPES_H

#include "jc_assert.h"

typedef unsigned char jc_u8;
typedef signed char jc_s8;
typedef unsigned short jc_u16;
typedef signed short jc_s16;
typedef unsigned int jc_u32;
typedef signed int jc_s32;

typedef struct {
  jc_u32 lo;
  jc_u32 hi;
} jc_u64;

typedef struct {
  jc_s32 lo;
  jc_s32 hi;
} jc_s64;

JC_STATIC_ASSERT(jc_u8_size, sizeof(jc_u8) == 1);
JC_STATIC_ASSERT(jc_s8_size, sizeof(jc_s8) == 1);
JC_STATIC_ASSERT(jc_u16_size, sizeof(jc_u16) == 2);
JC_STATIC_ASSERT(jc_s16_size, sizeof(jc_s16) == 2);
JC_STATIC_ASSERT(jc_u32_size, sizeof(jc_u32) == 4);
JC_STATIC_ASSERT(jc_s32_size, sizeof(jc_s32) == 4);
JC_STATIC_ASSERT(jc_u64_size, sizeof(jc_u64) == 8);
JC_STATIC_ASSERT(jc_s64_size, sizeof(jc_s64) == 8);

JC_STATIC_ASSERT(jc_s8_signed, ((jc_s8)-1) < 0);
JC_STATIC_ASSERT(jc_s16_signed, ((jc_s16)-1) < 0);
JC_STATIC_ASSERT(jc_s32_signed, ((jc_s32)-1) < 0);

JC_STATIC_ASSERT(jc_u64_packed, JC_OFFSETOF(jc_u64, hi) == 4);
JC_STATIC_ASSERT(jc_s64_packed, JC_OFFSETOF(jc_s64, hi) == 4);

#endif /* JC_TYPES_H */
