#ifndef PAL_ROMWBW_H
#define PAL_ROMWBW_H

#include "jc_contracts.h"
#include "jc_error.h"
#include "jc_pal.h"
#include "jc_types.h"

typedef struct {
  void *ctx;
  const char *platform_id;
  const char *platform_version;
  jc_u32 platform_caps;
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
  const jc_mem_region_header_v1 *(*memmap_get)(void *ctx);
  const jc_bdt_header_v1 *bdt;
  const jc_capset_v1 *capset;
} jc_pal_romwbw_hooks;

void jc_pal_romwbw_set_hooks(const jc_pal_romwbw_hooks *hooks);
void jc_pal_romwbw_bind(void);

#endif /* PAL_ROMWBW_H */
