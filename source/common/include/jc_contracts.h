#ifndef JC_CONTRACTS_H
#define JC_CONTRACTS_H

#include "jc_types.h"

typedef struct {
  jc_u32 signature;
  jc_u16 version;
  jc_u16 size_bytes;
  jc_u64 discovery_ptr;
  jc_u64 reserved0;
} jc_bsp_anchor_v1;

typedef struct {
  jc_u32 signature;
  jc_u16 table_version;
  jc_u16 table_size;
  jc_u8 cpu_ladder_id;
  jc_u8 fpu_ladder_id;
  jc_u8 presented_cpu_tier;
  jc_u8 presented_fpu_tier;
  jc_u8 profile_id;
  jc_u8 reserved0[3];
  jc_u64 topology_table_ptr;
  jc_u64 bdt_ptr;
  jc_u64 limits_table_ptr;
  jc_u64 cpu_feature_bitmap_ptr;
  jc_u64 fpu_feature_bitmap_ptr;
  jc_u64 peripheral_feature_bitmap_ptr;
} jc_discovery_table_v1;

typedef struct {
  jc_u32 queue_submit_depth;
  jc_u32 queue_complete_depth;
  jc_u16 contexts;
  jc_u16 vector_lanes;
  jc_u16 tensor_rank;
  jc_u16 reserved0;
  jc_u16 max_cores;
  jc_u16 max_threads;
  jc_u32 reserved1[3];
} jc_limits_table_v1;

typedef struct {
  jc_u32 word0;
  jc_u32 word1;
  jc_u32 word2;
  jc_u32 word3;
} jc_feature_bitmap_v1;

typedef struct {
  jc_u8 previous_tier;
  jc_u8 previous_modeflags;
  jc_u16 reserved0;
  jc_u32 reserved1;
  jc_u64 return_pc;
} jc_modeframe_v1;

typedef struct {
  jc_u16 version;
  jc_u16 size_bytes;
  jc_u8 target_tier;
  jc_u8 reserved0;
  jc_u16 flags;
  jc_u64 entry_vector;
  jc_u64 return_pc;
  jc_u32 error_code;
  jc_u32 reserved1;
} jc_mode_abi_v1;

typedef struct {
  jc_u32 signature;
  jc_u16 version;
  jc_u16 size_bytes;
  jc_u8 cpu_ladder_id;
  jc_u8 fpu_ladder_id;
  jc_u8 presented_cpu_tier;
  jc_u8 presented_fpu_tier;
  jc_u8 profile_id;
  jc_u8 reserved0[3];
  jc_u32 cpu_features[4];
  jc_u32 fpu_features[4];
  jc_u32 periph_features[4];
  jc_u64 topology_table_ptr;
  jc_u64 bdt_ptr;
  jc_u64 limits_table_ptr;
  jc_u64 mem_region_table_ptr;
  jc_u64 tier_host_table_ptr;
  jc_u16 max_devices;
  jc_u16 max_dma_segments;
  jc_u16 max_bdt_entries;
  jc_u16 max_irq_routes;
  jc_u32 reserved1;
  jc_u32 reserved2[3];
} jc_capset_v1;

typedef struct {
  jc_u32 signature;
  jc_u16 header_version;
  jc_u16 header_size;
  jc_u16 entry_size;
  jc_u16 entry_count;
  jc_u32 total_size;
} jc_topology_header_v1;

typedef struct {
  jc_u16 socket_id;
  jc_u16 cluster_id;
  jc_u16 core_id;
  jc_u16 thread_id;
  jc_u16 cache_l1_id;
  jc_u16 cache_l2_id;
  jc_u16 cache_l3_id;
  jc_u16 coherence_domain_id;
  jc_u16 numa_node_id;
  jc_u16 reserved0[7];
} jc_topology_entry_v1;

typedef struct {
  jc_u32 signature;
  jc_u16 header_version;
  jc_u16 header_size;
  jc_u16 entry_size;
  jc_u16 entry_count;
  jc_u32 total_size;
} jc_tier_host_header_v1;

typedef struct {
  jc_u16 socket_id;
  jc_u16 cluster_id;
  jc_u16 core_id;
  jc_u16 reserved0;
  jc_u16 tier_mask;
  jc_u16 reserved1;
  jc_u32 reserved2;
} jc_tier_host_entry_v1;

typedef struct {
  jc_u32 signature;
  jc_u16 header_version;
  jc_u16 header_size;
  jc_u16 entry_size;
  jc_u16 entry_count;
  jc_u32 total_size;
} jc_mem_region_header_v1;

typedef struct {
  jc_u8 region_kind;
  jc_u8 region_attrs;
  jc_u16 reserved0;
  jc_u64 base_addr;
  jc_u64 size_bytes;
  jc_u32 reserved1;
} jc_mem_region_entry_v1;

typedef struct {
  jc_u32 signature;
  jc_u16 header_version;
  jc_u16 header_size;
  jc_u16 entry_size;
  jc_u16 entry_count;
  jc_u32 total_size;
} jc_bdt_header_v1;

typedef struct {
  jc_u16 desc_version;
  jc_u16 desc_size_bytes;
  jc_u16 class_id;
  jc_u16 subclass_id;
  jc_u16 instance_id;
  jc_u16 device_version;
  jc_u32 caps0;
  jc_u32 caps1;
  jc_u16 irq_route_offset;
  jc_u16 irq_route_count;
  jc_u64 mmio_base;
  jc_u32 mmio_size;
  jc_u32 io_port_base;
  jc_u16 io_port_size;
  jc_u16 block_sector_size;
  jc_u16 cai_queue_count;
  jc_u16 cai_doorbell_offset;
  jc_u64 aux_ptr;
  jc_u32 aux_size;
  jc_u16 aux_type;
  jc_u16 reserved0;
} jc_bdt_entry_v1;

typedef struct {
  jc_u16 domain_id;
  jc_u16 irq_line;
  jc_u16 flags;
  jc_u16 reserved0;
} jc_bdt_irq_route_v1;

typedef struct {
  jc_u32 crc32;
} jc_bdt_footer_v1;

typedef struct {
  jc_u16 desc_version;
  jc_u16 desc_size_dw;
  jc_u32 opcode;
  jc_u32 flags;
  jc_u16 context_id;
  jc_u16 operand_count;
  jc_u32 tag;
  jc_u8 opcode_group;
  jc_u8 format_primary;
  jc_u8 format_aux;
  jc_u8 format_flags;
  jc_u64 operands_ptr;
  jc_u64 result_ptr;
  jc_u32 result_len;
  jc_u32 result_stride;
  jc_u64 tensor_desc_ptr;
  jc_u16 tensor_desc_len;
  jc_u8 tensor_rank;
  jc_u8 tensor_desc_flags;
  jc_u32 reserved2;
} jc_cai_submit_desc_v1;

typedef struct {
  jc_u64 ptr;
  jc_u32 len;
  jc_u32 stride;
  jc_u32 flags;
  jc_u32 reserved0;
  jc_u64 reserved1;
} jc_cai_operand_desc_v1;

typedef struct {
  jc_u16 desc_version;
  jc_u16 desc_size_dw;
  jc_u8 rank;
  jc_u8 elem_format;
  jc_u16 reserved0;
  jc_u32 flags;
  jc_u32 shape0;
  jc_u32 shape1;
  jc_u32 shape2;
  jc_u32 shape3;
  jc_u32 stride0;
  jc_u32 stride1;
  jc_u32 stride2;
  jc_u32 stride3;
  jc_u32 reserved1;
  jc_u64 reserved2;
  jc_u64 reserved3;
} jc_cai_tensor_desc_v1;

typedef struct {
  jc_u32 tag;
  jc_u16 status;
  jc_u16 ext_status;
  jc_u32 bytes_written;
  jc_u32 reserved0;
} jc_cai_comp_rec_v1;

typedef struct {
  jc_u32 signature;
  jc_u16 header_version;
  jc_u16 header_size;
  jc_u8 min_cpu_tier;
  jc_u8 reserved0;
  jc_u16 flags;
  jc_u32 load_policy;
  jc_u64 load_addr;
  jc_u32 entry_offset;
  jc_u32 bss_size;
  jc_u32 image_size;
  jc_u32 tlv_size;
  jc_u32 crc32;
  jc_u32 reserved1;
} jc_jcom_header_v1;

typedef struct {
  jc_u32 signature;
  jc_u16 version;
  jc_u16 size_bytes;
  jc_u16 sector_size;
  jc_u16 sectors_per_block;
  jc_u16 dir_entry_count;
  jc_u16 reserved0;
  jc_u32 total_sectors;
  jc_u32 dir_start_lba;
  jc_u32 data_start_lba;
  jc_u32 alloc_block_count;
  jc_u32 volume_id;
  jc_u32 flags;
  jc_u32 crc32;
  jc_u32 reserved1;
  jc_u32 reserved2[4];
} jc_cpmx_superblock_v1;

typedef struct {
  jc_u8 user;
  jc_u8 name[8];
  jc_u8 ext[3];
  jc_u8 flags;
  jc_u8 extent;
  jc_u8 reserved0;
  jc_u8 record_count;
  jc_u16 block_ptrs[8];
} jc_cpmx_dir_entry_v1;

#endif /* JC_CONTRACTS_H */
