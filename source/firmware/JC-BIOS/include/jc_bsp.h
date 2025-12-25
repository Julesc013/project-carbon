#ifndef JC_BSP_H
#define JC_BSP_H

#include "jc_types.h"

#define JC_PLATFORM_DESC_V1_SIGNATURE 0x544C504Au
#define JC_PLATFORM_DESC_V1_VERSION 1u

typedef struct {
  jc_u32 signature;
  jc_u16 version;
  jc_u16 size_bytes;
  jc_u8 profile_id;
  jc_u8 reserved0[3];
  jc_u8 name[16];
} jc_platform_desc_v1;

extern const jc_platform_desc_v1 jc_platform_desc;
extern const jc_u16 jc_bsp_anchor_addr;
extern const jc_u16 jc_bsp_stack_top;

#endif /* JC_BSP_H */
