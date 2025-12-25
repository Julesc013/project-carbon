#include "panic.h"

#include "bios_services.h"
#include "jc_dos_util.h"
#include "log.h"

void jc_dos_panic(jc_error_t err) {
  jc_dos_log("JC-DOS PANIC ");
  jc_dos_log_hex16(err);
  jc_dos_log("\n");
  jc_bios_console_write("RETURNING TO BIOS\n");
}
