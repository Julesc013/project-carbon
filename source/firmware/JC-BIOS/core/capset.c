#include "jc_capset.h"

#include "jc_bios.h"
#include "jc_contracts_autogen.h"
#include "jc_util.h"

static void jc_copy_feature_bitmap(jc_u32 out[4], jc_u64 ptr) {
  const jc_feature_bitmap_v1 *bitmap;
  if (ptr.hi != 0u || ptr.lo == 0u) {
    out[0] = 0;
    out[1] = 0;
    out[2] = 0;
    out[3] = 0;
    return;
  }
  bitmap = (const jc_feature_bitmap_v1 *)(unsigned long)ptr.lo;
  out[0] = bitmap->word0;
  out[1] = bitmap->word1;
  out[2] = bitmap->word2;
  out[3] = bitmap->word3;
}

static jc_u16 jc_sum_irq_routes(const jc_bdt_index *index) {
  jc_u16 total = 0;
  jc_u16 i;
  if (!index) {
    return 0;
  }
  for (i = 0; i < index->entry_count; ++i) {
    const jc_bdt_entry_v1 *entry = index->index[i].entry;
    if (entry) {
      total = (jc_u16)(total + entry->irq_route_count);
    }
  }
  return total;
}

jc_error_t jc_capset_init(jc_capset_v1 *capset,
                          const jc_discovery_table_v1 *discovery,
                          const jc_bdt_index *bdt_index) {
  if (!capset || !discovery) {
    return JC_E_INTERNAL_ASSERT;
  }

  jc_memset(capset, 0, sizeof(*capset));
  capset->signature = JC_MAGIC_CAPSET;
  capset->version = JC_CAPSET_V1_VERSION;
  capset->size_bytes = JC_CAPSET_V1_SIZE;
  capset->cpu_ladder_id = discovery->cpu_ladder_id;
  capset->fpu_ladder_id = discovery->fpu_ladder_id;
  capset->presented_cpu_tier = discovery->presented_cpu_tier;
  capset->presented_fpu_tier = discovery->presented_fpu_tier;
  capset->profile_id = discovery->profile_id;

  jc_copy_feature_bitmap(capset->cpu_features,
                          discovery->cpu_feature_bitmap_ptr);
  jc_copy_feature_bitmap(capset->fpu_features,
                          discovery->fpu_feature_bitmap_ptr);
  jc_copy_feature_bitmap(capset->periph_features,
                          discovery->peripheral_feature_bitmap_ptr);

  capset->topology_table_ptr = discovery->topology_table_ptr;
  capset->bdt_ptr = discovery->bdt_ptr;
  capset->limits_table_ptr = discovery->limits_table_ptr;
  capset->mem_region_table_ptr = jc_u64_make(0, 0);
  capset->tier_host_table_ptr = jc_u64_make(0, 0);

  if (bdt_index) {
    capset->max_devices = bdt_index->entry_count;
    capset->max_bdt_entries = bdt_index->entry_count;
    capset->max_irq_routes = jc_sum_irq_routes(bdt_index);
  }
  capset->max_dma_segments = 0;

  return JC_E_OK;
}
