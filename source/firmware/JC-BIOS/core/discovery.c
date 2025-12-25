#include "jc_discovery.h"

#include "jc_bsp.h"
#include "jc_contracts_autogen.h"
#include "jc_offsets_autogen.h"
#include "jc_util.h"

static const jc_bsp_anchor_v1 *jc_anchor_from_bsp(void) {
  const unsigned long addr = (unsigned long)jc_bsp_anchor_addr;
  return (const jc_bsp_anchor_v1 *)addr;
}

static const jc_discovery_table_v1 *jc_discovery_from_anchor(
    const jc_bsp_anchor_v1 *anchor) {
  const jc_u64 ptr = anchor->discovery_ptr;
  const unsigned long addr = (unsigned long)ptr.lo;
  if (ptr.hi != 0u) {
    return 0;
  }
  if (addr == 0ul) {
    return 0;
  }
  return (const jc_discovery_table_v1 *)addr;
}

jc_error_t jc_discovery_init(const jc_bsp_anchor_v1 **anchor_out,
                             const jc_discovery_table_v1 **table_out) {
  const jc_bsp_anchor_v1 *anchor = jc_anchor_from_bsp();
  const jc_discovery_table_v1 *table = 0;

  if (!anchor_out || !table_out) {
    return JC_E_INTERNAL_ASSERT;
  }

  if (!anchor) {
    return JC_E_BOOT_BSP_MISSING;
  }

  if (anchor->signature != JC_MAGIC_BSP_ANCHOR) {
    return JC_E_BOOT_BSP_BAD_SIGNATURE;
  }
  if (anchor->version != JC_BSP_ANCHOR_V1_VERSION) {
    return JC_E_DISCOVERY_BAD_VERSION;
  }
  if (anchor->size_bytes != JC_STRUCT_BSP_ANCHOR_V1_SIZE) {
    return JC_E_DISCOVERY_BAD_SIZE;
  }
  if (!jc_u64_is_zero(anchor->reserved0)) {
    return JC_E_DISCOVERY_BAD_SIZE;
  }

  table = jc_discovery_from_anchor(anchor);
  if (!table) {
    return JC_E_BOOT_DISCOVERY_MISSING;
  }
  if (table->signature != JC_MAGIC_DISCOVERY_TABLE) {
    return JC_E_DISCOVERY_BAD_SIGNATURE;
  }
  if (table->table_version != JC_DISCOVERY_TABLE_V1_VERSION) {
    return JC_E_DISCOVERY_BAD_VERSION;
  }
  if (table->table_size != JC_DISCOVERY_TABLE_V1_SIZE) {
    return JC_E_DISCOVERY_BAD_SIZE;
  }
  if (table->reserved0[0] != 0 || table->reserved0[1] != 0 ||
      table->reserved0[2] != 0) {
    return JC_E_DISCOVERY_BAD_SIZE;
  }

  *anchor_out = anchor;
  *table_out = table;
  return JC_E_OK;
}
