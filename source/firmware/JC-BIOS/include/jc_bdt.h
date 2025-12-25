#ifndef JC_BDT_H
#define JC_BDT_H

#include "jc_contracts.h"
#include "jc_error.h"

#define JC_BDT_INDEX_MAX 32u

typedef struct {
  jc_u16 class_id;
  jc_u16 instance_id;
  const jc_bdt_entry_v1 *entry;
} jc_bdt_index_entry;

typedef struct {
  const jc_bdt_header_v1 *header;
  const jc_bdt_entry_v1 *entries;
  jc_u16 entry_count;
  jc_u16 index_count;
  jc_u32 crc32;
  jc_bdt_index_entry index[JC_BDT_INDEX_MAX];
} jc_bdt_index;

jc_error_t jc_bdt_init(jc_bdt_index *index, jc_u64 bdt_ptr);
const jc_bdt_entry_v1 *jc_bdt_find(const jc_bdt_index *index,
                                   jc_u16 class_id,
                                   jc_u16 instance_id);

#endif /* JC_BDT_H */
