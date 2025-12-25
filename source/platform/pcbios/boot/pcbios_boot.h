#ifndef PCBIOS_BOOT_H
#define PCBIOS_BOOT_H

#include "jc_dos_handoff.h"
#include "jc_error.h"
#include "jc_pal.h"
#include "jc_types.h"

typedef struct {
  void *ctx;
  jc_error_t (*read_sectors)(void *ctx,
                             jc_u32 lba,
                             jc_u8 *dst,
                             jc_u16 count512);
  jc_error_t (*console_write)(void *ctx, const char *data, jc_u16 len);
  void (*jump)(void *ctx, jc_u32 addr);
} jc_pcbios_boot_ops;

typedef void (*jc_pcbios_kernel_entry_fn)(const jc_dos_handoff_v1 *handoff);

jc_error_t jc_pcbios_stage1_load(const jc_pcbios_boot_ops *ops,
                                 jc_u32 lba_start,
                                 jc_u16 sectors,
                                 jc_u32 load_addr);

jc_error_t jc_pcbios_stage2_prepare(jc_dos_handoff_v1 *handoff,
                                    const jc_pal_desc *pal,
                                    jc_u32 tpa_base,
                                    jc_u32 tpa_size,
                                    jc_u64 services_ptr);

jc_error_t jc_pcbios_stage2_handoff(const jc_pcbios_boot_ops *ops,
                                    jc_pcbios_kernel_entry_fn entry,
                                    jc_u32 tpa_base,
                                    jc_u32 tpa_size,
                                    jc_u64 services_ptr);

#endif /* PCBIOS_BOOT_H */
