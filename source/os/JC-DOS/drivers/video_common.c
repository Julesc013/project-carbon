#include "video_common.h"

#include "jc_contracts_autogen.h"

const jc_bdt_entry_v1 *jc_video_find_pio(const jc_bdt_header_v1 *bdt,
                                         jc_u16 subclass_id) {
  jc_u32 i;
  if (!bdt) {
    return 0;
  }
  if (bdt->signature != JC_MAGIC_BDT ||
      bdt->header_version != JC_BDT_HEADER_V1_VERSION ||
      bdt->header_size != JC_BDT_HEADER_V1_SIZE ||
      bdt->entry_size != JC_BDT_ENTRY_V1_SIZE) {
    return 0;
  }
  for (i = 0; i < bdt->entry_count; ++i) {
    const jc_u8 *base = (const jc_u8 *)bdt;
    const jc_u8 *ptr = base + bdt->header_size + i * bdt->entry_size;
    const jc_bdt_entry_v1 *entry = (const jc_bdt_entry_v1 *)ptr;
    if (entry->class_id == JC_DEVCLASS_PIO &&
        entry->subclass_id == subclass_id) {
      return entry;
    }
  }
  return 0;
}
