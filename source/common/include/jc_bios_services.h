#ifndef JC_BIOS_SERVICES_H
#define JC_BIOS_SERVICES_H

#include "jc_error.h"
#include "jc_types.h"

#define JC_BIOS_SERVICES_V1_SIGNATURE 0x4F49424Au /* "JBIO" */
#define JC_BIOS_SERVICES_V1_VERSION 1u

typedef jc_error_t (*jc_bios_console_putc_fn)(char c);
typedef jc_error_t (*jc_bios_console_write_fn)(const char *s);
typedef jc_error_t (*jc_bios_console_readline_fn)(char *buf, jc_u32 max_len);

typedef jc_error_t (*jc_bios_block_open_fn)(jc_u16 instance);
typedef jc_error_t (*jc_bios_block_read_fn)(jc_u32 lba, jc_u8 *buf,
                                            jc_u16 count512);
typedef jc_error_t (*jc_bios_block_write_fn)(jc_u32 lba, const jc_u8 *buf,
                                             jc_u16 count512);
typedef jc_error_t (*jc_bios_block_test_timeout_fn)(jc_u32 timeout_ticks);

typedef jc_u64 (*jc_bios_timer_ticks_fn)(void);
typedef jc_u32 (*jc_bios_timer_tick_hz_fn)(void);

typedef void (*jc_bios_reboot_fn)(void);

typedef struct {
  jc_u32 signature;
  jc_u16 version;
  jc_u16 size_bytes;
  jc_bios_console_putc_fn console_putc;
  jc_bios_console_write_fn console_write;
  jc_bios_console_readline_fn console_readline;
  jc_bios_block_open_fn block_open;
  jc_bios_block_read_fn block_read;
  jc_bios_block_write_fn block_write;
  jc_bios_block_test_timeout_fn block_test_timeout;
  jc_bios_timer_ticks_fn timer_ticks;
  jc_bios_timer_tick_hz_fn timer_tick_hz;
  jc_bios_reboot_fn reboot;
  jc_u32 reserved0;
  jc_u32 reserved1;
} jc_bios_services_v1;

#endif /* JC_BIOS_SERVICES_H */
