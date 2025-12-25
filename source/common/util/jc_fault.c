#include "jc_fault.h"

static jc_u32 g_fault_mask = 0u;

void jc_fault_set(jc_u32 mask) { g_fault_mask |= mask; }

void jc_fault_clear(jc_u32 mask) { g_fault_mask &= ~mask; }

jc_u32 jc_fault_get(void) { return g_fault_mask; }

int jc_fault_active(jc_u32 mask) { return (g_fault_mask & mask) != 0u; }

int jc_fault_consume(jc_u32 mask) {
  if ((g_fault_mask & mask) == 0u) {
    return 0;
  }
  g_fault_mask &= ~mask;
  return 1;
}
