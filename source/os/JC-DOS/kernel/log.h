#ifndef JC_DOS_LOG_H
#define JC_DOS_LOG_H

#include "jc_types.h"

void jc_dos_log(const char *s);
void jc_dos_log_hex16(jc_u16 value);
void jc_dos_log_hex32(jc_u32 value);
void jc_dos_log_lf(void);

#endif /* JC_DOS_LOG_H */
