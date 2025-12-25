#ifndef JC_FAULT_H
#define JC_FAULT_H

#include "jc_types.h"

#define JC_FAULT_IO_TIMEOUT (1u << 0)
#define JC_FAULT_PARTIAL_READ (1u << 1)
#define JC_FAULT_SPURIOUS_IRQ (1u << 2)
#define JC_FAULT_BAD_SECTOR (1u << 3)
#define JC_FAULT_MODEUP_FAIL (1u << 4)

void jc_fault_set(jc_u32 mask);
void jc_fault_clear(jc_u32 mask);
jc_u32 jc_fault_get(void);
int jc_fault_active(jc_u32 mask);
int jc_fault_consume(jc_u32 mask);

#endif /* JC_FAULT_H */
