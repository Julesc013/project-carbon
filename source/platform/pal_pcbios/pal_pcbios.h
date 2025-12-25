#ifndef PAL_PCBIOS_H
#define PAL_PCBIOS_H

#include "jc_contracts.h"
#include "jc_error.h"
#include "jc_pal.h"
#include "jc_types.h"

typedef struct {
  void *ctx;
  const char *platform_id;
  const char *platform_version;
  jc_u32 platform_caps;
  jc_u8 cpu_ladder_id;
  jc_u8 fpu_ladder_id;
  jc_u8 presented_cpu_tier;
  jc_u8 presented_fpu_tier;
  jc_u8 profile_id;
  jc_error_t (*console_write)(void *ctx, const char *data, jc_u32 len);
  jc_error_t (*console_read)(void *ctx,
                             char *out,
                             jc_u32 len,
                             jc_u32 *out_len);
  jc_error_t (*block_read)(void *ctx,
                           jc_u32 lba,
                           jc_u8 *buf,
                           jc_u16 count512);
  jc_error_t (*block_write)(void *ctx,
                            jc_u32 lba,
                            const jc_u8 *buf,
                            jc_u16 count512);
  jc_error_t (*block_get_params)(void *ctx, jc_pal_block_params *out_params);
  jc_u64 (*timer_ticks)(void *ctx);
  jc_u32 (*timer_hz)(void *ctx);
  jc_error_t (*keyboard_read)(void *ctx, jc_pal_key_event *out_event);
  int (*keyboard_poll)(void *ctx, jc_pal_key_event *out_event);
  const jc_mem_region_header_v1 *(*memmap_get)(void *ctx);
} jc_pal_pcbios_hooks;

void jc_pal_pcbios_set_hooks(const jc_pal_pcbios_hooks *hooks);
void jc_pal_pcbios_bind(void);

#endif /* PAL_PCBIOS_H */
