#ifndef JC_BIOS_H
#define JC_BIOS_H

#include "jc_bdt.h"
#include "jc_contracts.h"
#include "jc_error.h"
#include "jc_types.h"

typedef enum {
  JC_BOOT_PHASE_RESET = 0,
  JC_BOOT_PHASE_DISCOVERY = 1,
  JC_BOOT_PHASE_BDT = 2,
  JC_BOOT_PHASE_TIMER = 3,
  JC_BOOT_PHASE_CONSOLE = 4,
  JC_BOOT_PHASE_CAPSET = 5,
  JC_BOOT_PHASE_MONITOR = 6,
  JC_BOOT_PHASE_MODE = 7
} jc_boot_phase_t;

void jc_bios_p0_entry(void);

void jc_boot_set_phase(jc_boot_phase_t phase);
jc_boot_phase_t jc_boot_get_phase(void);
void jc_boot_set_error(jc_error_t err);
jc_error_t jc_boot_get_error(void);
const char *jc_boot_phase_name(jc_boot_phase_t phase);
const char *jc_error_name(jc_error_t err);

const jc_capset_v1 *jc_boot_capset(void);
jc_u32 jc_boot_capset_crc32(void);
jc_u32 jc_boot_bdt_crc32(void);
const jc_bdt_index *jc_boot_bdt_index(void);

#endif /* JC_BIOS_H */
