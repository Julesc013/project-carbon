#ifndef JC_DOS_BIOS_SERVICES_H
#define JC_DOS_BIOS_SERVICES_H

#include "jc_bios_services.h"
#include "jc_error.h"
#include "jc_types.h"

jc_error_t jc_bios_services_init(const jc_bios_services_v1 *services);
const jc_bios_services_v1 *jc_bios_services(void);

jc_error_t jc_bios_console_putc(char c);
jc_error_t jc_bios_console_write(const char *s);
jc_error_t jc_bios_console_readline(char *buf, jc_u32 max_len);

jc_error_t jc_bios_block_open(jc_u16 instance);
jc_error_t jc_bios_block_read(jc_u32 lba, jc_u8 *buf, jc_u16 count512);
jc_error_t jc_bios_block_write(jc_u32 lba, const jc_u8 *buf, jc_u16 count512);
jc_error_t jc_bios_block_test_timeout(jc_u32 timeout_ticks);

jc_u64 jc_bios_timer_ticks(void);
jc_u32 jc_bios_timer_tick_hz(void);

void jc_bios_reboot(void);

#endif /* JC_DOS_BIOS_SERVICES_H */
