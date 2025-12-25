#ifndef Z80_BOOT_H
#define Z80_BOOT_H

#include "jc_error.h"
#include "jc_types.h"

typedef struct {
  void *ctx;
  jc_error_t (*serial_read)(void *ctx, jc_u8 *out_byte);
  jc_error_t (*serial_write)(void *ctx, jc_u8 value);
  jc_error_t (*block_read)(void *ctx,
                           jc_u32 lba,
                           jc_u8 *dst,
                           jc_u16 count512);
  void (*jump)(void *ctx, jc_u32 addr);
} jc_z80_boot_ops;

jc_error_t jc_z80_serial_loader(const jc_z80_boot_ops *ops,
                                jc_u32 load_addr,
                                jc_u32 max_bytes);

jc_error_t jc_z80_disk_boot(const jc_z80_boot_ops *ops,
                            jc_u32 load_addr,
                            jc_u16 sectors);

jc_error_t jc_z80_romwbw_chainload(const jc_z80_boot_ops *ops,
                                   jc_u32 entry_addr);

#endif /* Z80_BOOT_H */
