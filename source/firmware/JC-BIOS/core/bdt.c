#include "jc_bdt.h"

#include "jc_contracts_autogen.h"
#include "jc_util.h"

static const jc_bdt_header_v1 *jc_bdt_base_from_ptr(jc_u64 ptr) {
  if (ptr.hi != 0u || ptr.lo == 0u) {
    return 0;
  }
  return (const jc_bdt_header_v1 *)(unsigned long)ptr.lo;
}

static int jc_bdt_validate_entry(const jc_bdt_entry_v1 *entry) {
  if (entry->desc_version != JC_BDT_ENTRY_V1_VERSION) {
    return 0;
  }
  if (entry->desc_size_bytes != JC_BDT_ENTRY_V1_SIZE) {
    return 0;
  }
  if (entry->reserved0 != 0u) {
    return 0;
  }
  if (entry->mmio_size != 0u && entry->mmio_base.lo == 0u &&
      entry->mmio_base.hi == 0u) {
    return 0;
  }
  if (entry->io_port_size != 0u && entry->io_port_base == 0u) {
    return 0;
  }
  if (entry->block_sector_size != 0u &&
      (entry->block_sector_size & 0x1FFu) != 0u) {
    return 0;
  }
  if (entry->irq_route_offset != 0u &&
      (entry->irq_route_offset & 0x1u) != 0u) {
    return 0;
  }
  return 1;
}

jc_error_t jc_bdt_init(jc_bdt_index *index, jc_u64 bdt_ptr) {
  const jc_bdt_header_v1 *header = jc_bdt_base_from_ptr(bdt_ptr);
  const jc_bdt_entry_v1 *entries = 0;
  const jc_bdt_footer_v1 *footer = 0;
  const jc_u8 *bytes = 0;
  jc_u32 expected_min = 0;
  jc_u32 routes_end_max = 0;
  jc_u32 expected_total = 0;
  jc_u32 crc_calc = 0;
  jc_u32 i;

  if (!index) {
    return JC_E_INTERNAL_ASSERT;
  }

  if (!header) {
    return JC_E_BDT_BAD_SIZE;
  }

  if (header->signature != JC_MAGIC_BDT) {
    return JC_E_BDT_BAD_SIGNATURE;
  }
  if (header->header_version != JC_BDT_HEADER_V1_VERSION) {
    return JC_E_BDT_BAD_VERSION;
  }
  if (header->header_size != JC_BDT_HEADER_V1_SIZE) {
    return JC_E_BDT_BAD_SIZE;
  }
  if (header->entry_size != JC_BDT_ENTRY_V1_SIZE) {
    return JC_E_BDT_BAD_SIZE;
  }

  expected_min = (jc_u32)header->header_size +
                 (jc_u32)header->entry_count * (jc_u32)header->entry_size +
                 (jc_u32)JC_BDT_FOOTER_V1_SIZE;
  if (header->total_size < expected_min) {
    return JC_E_BDT_BAD_SIZE;
  }

  bytes = (const jc_u8 *)header;
  routes_end_max = (jc_u32)header->header_size +
                   (jc_u32)header->entry_count * (jc_u32)header->entry_size;
  footer = (const jc_bdt_footer_v1 *)(bytes + header->total_size -
                                      JC_BDT_FOOTER_V1_SIZE);
  crc_calc = jc_crc32(bytes, header->total_size - JC_BDT_FOOTER_V1_SIZE);
  if (footer->crc32 != crc_calc) {
    return JC_E_BDT_BAD_CHECKSUM;
  }

  entries = (const jc_bdt_entry_v1 *)(bytes + header->header_size);
  if (header->entry_count > JC_BDT_INDEX_MAX) {
    return JC_E_BDT_BAD_SIZE;
  }

  for (i = 0; i < header->entry_count; ++i) {
    const jc_bdt_entry_v1 *entry =
        (const jc_bdt_entry_v1 *)((const jc_u8 *)entries +
                                  i * header->entry_size);
    if (!jc_bdt_validate_entry(entry)) {
      return JC_E_BDT_BAD_SIZE;
    }
    if (entry->irq_route_count != 0u) {
      jc_u32 route_bytes =
          (jc_u32)entry->irq_route_count * (jc_u32)JC_BDT_IRQ_ROUTE_V1_SIZE;
      jc_u32 route_end = (jc_u32)entry->irq_route_offset + route_bytes;
      jc_u32 entries_end =
          (jc_u32)header->header_size +
          (jc_u32)header->entry_count * (jc_u32)header->entry_size;
      if (entry->irq_route_offset < entries_end) {
        return JC_E_BDT_BAD_SIZE;
      }
      if (route_end > (header->total_size - JC_BDT_FOOTER_V1_SIZE)) {
        return JC_E_BDT_BAD_SIZE;
      }
      if (route_end > routes_end_max) {
        routes_end_max = route_end;
      }
    }
    index->index[i].class_id = entry->class_id;
    index->index[i].instance_id = entry->instance_id;
    index->index[i].entry = entry;
  }

  expected_total = routes_end_max + JC_BDT_FOOTER_V1_SIZE;
  if (header->total_size != expected_total) {
    return JC_E_BDT_BAD_SIZE;
  }

  index->header = header;
  index->entries = entries;
  index->entry_count = header->entry_count;
  index->index_count = header->entry_count;
  index->crc32 = crc_calc;
  return JC_E_OK;
}

const jc_bdt_entry_v1 *jc_bdt_find(const jc_bdt_index *index,
                                   jc_u16 class_id,
                                   jc_u16 instance_id) {
  jc_u16 i;
  if (!index) {
    return 0;
  }
  for (i = 0; i < index->index_count; ++i) {
    if (index->index[i].class_id == class_id &&
        index->index[i].instance_id == instance_id) {
      return index->index[i].entry;
    }
  }
  return 0;
}
