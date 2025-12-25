#include "log.h"

#include "bios_services.h"
#include "jc_dos_util.h"

void jc_dos_log(const char *s) {
  jc_bios_console_write(s);
}

void jc_dos_log_hex16(jc_u16 value) {
  char buf[4];
  jc_dos_u16_to_hex(buf, value);
  jc_bios_console_putc(buf[0]);
  jc_bios_console_putc(buf[1]);
  jc_bios_console_putc(buf[2]);
  jc_bios_console_putc(buf[3]);
}

void jc_dos_log_hex32(jc_u32 value) {
  char buf[8];
  jc_dos_u32_to_hex(buf, value);
  jc_bios_console_putc(buf[0]);
  jc_bios_console_putc(buf[1]);
  jc_bios_console_putc(buf[2]);
  jc_bios_console_putc(buf[3]);
  jc_bios_console_putc(buf[4]);
  jc_bios_console_putc(buf[5]);
  jc_bios_console_putc(buf[6]);
  jc_bios_console_putc(buf[7]);
}

void jc_dos_log_lf(void) {
  jc_bios_console_putc('\n');
}
