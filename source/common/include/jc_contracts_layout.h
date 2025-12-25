#ifndef JC_CONTRACTS_LAYOUT_H
#define JC_CONTRACTS_LAYOUT_H

#include "jc_assert.h"
#include "jc_contracts.h"
#include "jc_offsets_autogen.h"

JC_STATIC_ASSERT(bsp_anchor_size,
                 sizeof(jc_bsp_anchor_v1) == JC_STRUCT_BSP_ANCHOR_V1_SIZE);
JC_STATIC_ASSERT(bsp_anchor_align,
                 JC_ALIGNOF(jc_bsp_anchor_v1) == JC_STRUCT_BSP_ANCHOR_V1_ALIGN);
JC_STATIC_ASSERT(bsp_anchor_signature_off,
                 JC_OFFSETOF(jc_bsp_anchor_v1, signature) ==
                     JC_STRUCT_BSP_ANCHOR_V1_SIGNATURE_OFF);
JC_STATIC_ASSERT(bsp_anchor_version_off,
                 JC_OFFSETOF(jc_bsp_anchor_v1, version) ==
                     JC_STRUCT_BSP_ANCHOR_V1_VERSION_OFF);
JC_STATIC_ASSERT(bsp_anchor_size_bytes_off,
                 JC_OFFSETOF(jc_bsp_anchor_v1, size_bytes) ==
                     JC_STRUCT_BSP_ANCHOR_V1_SIZE_BYTES_OFF);
JC_STATIC_ASSERT(bsp_anchor_discovery_ptr_off,
                 JC_OFFSETOF(jc_bsp_anchor_v1, discovery_ptr) ==
                     JC_STRUCT_BSP_ANCHOR_V1_DISCOVERY_PTR_OFF);
JC_STATIC_ASSERT(bsp_anchor_reserved0_off,
                 JC_OFFSETOF(jc_bsp_anchor_v1, reserved0) ==
                     JC_STRUCT_BSP_ANCHOR_V1_RESERVED0_OFF);

JC_STATIC_ASSERT(discovery_table_size,
                 sizeof(jc_discovery_table_v1) ==
                     JC_STRUCT_DISCOVERY_TABLE_V1_SIZE);
JC_STATIC_ASSERT(discovery_table_align,
                 JC_ALIGNOF(jc_discovery_table_v1) ==
                     JC_STRUCT_DISCOVERY_TABLE_V1_ALIGN);
JC_STATIC_ASSERT(discovery_table_signature_off,
                 JC_OFFSETOF(jc_discovery_table_v1, signature) ==
                     JC_STRUCT_DISCOVERY_TABLE_V1_SIGNATURE_OFF);
JC_STATIC_ASSERT(discovery_table_table_version_off,
                 JC_OFFSETOF(jc_discovery_table_v1, table_version) ==
                     JC_STRUCT_DISCOVERY_TABLE_V1_TABLE_VERSION_OFF);
JC_STATIC_ASSERT(discovery_table_table_size_off,
                 JC_OFFSETOF(jc_discovery_table_v1, table_size) ==
                     JC_STRUCT_DISCOVERY_TABLE_V1_TABLE_SIZE_OFF);
JC_STATIC_ASSERT(discovery_table_cpu_ladder_id_off,
                 JC_OFFSETOF(jc_discovery_table_v1, cpu_ladder_id) ==
                     JC_STRUCT_DISCOVERY_TABLE_V1_CPU_LADDER_ID_OFF);
JC_STATIC_ASSERT(discovery_table_fpu_ladder_id_off,
                 JC_OFFSETOF(jc_discovery_table_v1, fpu_ladder_id) ==
                     JC_STRUCT_DISCOVERY_TABLE_V1_FPU_LADDER_ID_OFF);
JC_STATIC_ASSERT(discovery_table_presented_cpu_tier_off,
                 JC_OFFSETOF(jc_discovery_table_v1, presented_cpu_tier) ==
                     JC_STRUCT_DISCOVERY_TABLE_V1_PRESENTED_CPU_TIER_OFF);
JC_STATIC_ASSERT(discovery_table_presented_fpu_tier_off,
                 JC_OFFSETOF(jc_discovery_table_v1, presented_fpu_tier) ==
                     JC_STRUCT_DISCOVERY_TABLE_V1_PRESENTED_FPU_TIER_OFF);
JC_STATIC_ASSERT(discovery_table_profile_id_off,
                 JC_OFFSETOF(jc_discovery_table_v1, profile_id) ==
                     JC_STRUCT_DISCOVERY_TABLE_V1_PROFILE_ID_OFF);
JC_STATIC_ASSERT(discovery_table_reserved0_off,
                 JC_OFFSETOF(jc_discovery_table_v1, reserved0) ==
                     JC_STRUCT_DISCOVERY_TABLE_V1_RESERVED0_OFF);
JC_STATIC_ASSERT(discovery_table_topology_ptr_off,
                 JC_OFFSETOF(jc_discovery_table_v1, topology_table_ptr) ==
                     JC_STRUCT_DISCOVERY_TABLE_V1_TOPOLOGY_TABLE_PTR_OFF);
JC_STATIC_ASSERT(discovery_table_bdt_ptr_off,
                 JC_OFFSETOF(jc_discovery_table_v1, bdt_ptr) ==
                     JC_STRUCT_DISCOVERY_TABLE_V1_BDT_PTR_OFF);
JC_STATIC_ASSERT(discovery_table_limits_ptr_off,
                 JC_OFFSETOF(jc_discovery_table_v1, limits_table_ptr) ==
                     JC_STRUCT_DISCOVERY_TABLE_V1_LIMITS_TABLE_PTR_OFF);
JC_STATIC_ASSERT(discovery_table_cpu_feat_ptr_off,
                 JC_OFFSETOF(jc_discovery_table_v1, cpu_feature_bitmap_ptr) ==
                     JC_STRUCT_DISCOVERY_TABLE_V1_CPU_FEATURE_BITMAP_PTR_OFF);
JC_STATIC_ASSERT(discovery_table_fpu_feat_ptr_off,
                 JC_OFFSETOF(jc_discovery_table_v1, fpu_feature_bitmap_ptr) ==
                     JC_STRUCT_DISCOVERY_TABLE_V1_FPU_FEATURE_BITMAP_PTR_OFF);
JC_STATIC_ASSERT(
    discovery_table_periph_feat_ptr_off,
    JC_OFFSETOF(jc_discovery_table_v1, peripheral_feature_bitmap_ptr) ==
        JC_STRUCT_DISCOVERY_TABLE_V1_PERIPHERAL_FEATURE_BITMAP_PTR_OFF);

JC_STATIC_ASSERT(limits_table_size,
                 sizeof(jc_limits_table_v1) == JC_STRUCT_LIMITS_TABLE_V1_SIZE);
JC_STATIC_ASSERT(limits_table_align,
                 JC_ALIGNOF(jc_limits_table_v1) == JC_STRUCT_LIMITS_TABLE_V1_ALIGN);
JC_STATIC_ASSERT(limits_table_queue_submit_depth_off,
                 JC_OFFSETOF(jc_limits_table_v1, queue_submit_depth) ==
                     JC_STRUCT_LIMITS_TABLE_V1_QUEUE_SUBMIT_DEPTH_OFF);
JC_STATIC_ASSERT(limits_table_queue_complete_depth_off,
                 JC_OFFSETOF(jc_limits_table_v1, queue_complete_depth) ==
                     JC_STRUCT_LIMITS_TABLE_V1_QUEUE_COMPLETE_DEPTH_OFF);
JC_STATIC_ASSERT(limits_table_contexts_off,
                 JC_OFFSETOF(jc_limits_table_v1, contexts) ==
                     JC_STRUCT_LIMITS_TABLE_V1_CONTEXTS_OFF);
JC_STATIC_ASSERT(limits_table_vector_lanes_off,
                 JC_OFFSETOF(jc_limits_table_v1, vector_lanes) ==
                     JC_STRUCT_LIMITS_TABLE_V1_VECTOR_LANES_OFF);
JC_STATIC_ASSERT(limits_table_tensor_rank_off,
                 JC_OFFSETOF(jc_limits_table_v1, tensor_rank) ==
                     JC_STRUCT_LIMITS_TABLE_V1_TENSOR_RANK_OFF);
JC_STATIC_ASSERT(limits_table_reserved0_off,
                 JC_OFFSETOF(jc_limits_table_v1, reserved0) ==
                     JC_STRUCT_LIMITS_TABLE_V1_RESERVED0_OFF);
JC_STATIC_ASSERT(limits_table_max_cores_off,
                 JC_OFFSETOF(jc_limits_table_v1, max_cores) ==
                     JC_STRUCT_LIMITS_TABLE_V1_MAX_CORES_OFF);
JC_STATIC_ASSERT(limits_table_max_threads_off,
                 JC_OFFSETOF(jc_limits_table_v1, max_threads) ==
                     JC_STRUCT_LIMITS_TABLE_V1_MAX_THREADS_OFF);
JC_STATIC_ASSERT(limits_table_reserved1_off,
                 JC_OFFSETOF(jc_limits_table_v1, reserved1) ==
                     JC_STRUCT_LIMITS_TABLE_V1_RESERVED1_OFF);

JC_STATIC_ASSERT(feature_bitmap_size,
                 sizeof(jc_feature_bitmap_v1) ==
                     JC_STRUCT_FEATURE_BITMAP_V1_SIZE);
JC_STATIC_ASSERT(feature_bitmap_align,
                 JC_ALIGNOF(jc_feature_bitmap_v1) ==
                     JC_STRUCT_FEATURE_BITMAP_V1_ALIGN);
JC_STATIC_ASSERT(feature_bitmap_word0_off,
                 JC_OFFSETOF(jc_feature_bitmap_v1, word0) ==
                     JC_STRUCT_FEATURE_BITMAP_V1_WORD0_OFF);
JC_STATIC_ASSERT(feature_bitmap_word1_off,
                 JC_OFFSETOF(jc_feature_bitmap_v1, word1) ==
                     JC_STRUCT_FEATURE_BITMAP_V1_WORD1_OFF);
JC_STATIC_ASSERT(feature_bitmap_word2_off,
                 JC_OFFSETOF(jc_feature_bitmap_v1, word2) ==
                     JC_STRUCT_FEATURE_BITMAP_V1_WORD2_OFF);
JC_STATIC_ASSERT(feature_bitmap_word3_off,
                 JC_OFFSETOF(jc_feature_bitmap_v1, word3) ==
                     JC_STRUCT_FEATURE_BITMAP_V1_WORD3_OFF);

JC_STATIC_ASSERT(modeframe_size,
                 sizeof(jc_modeframe_v1) == JC_STRUCT_MODEFRAME_V1_SIZE);
JC_STATIC_ASSERT(modeframe_align,
                 JC_ALIGNOF(jc_modeframe_v1) == JC_STRUCT_MODEFRAME_V1_ALIGN);
JC_STATIC_ASSERT(modeframe_previous_tier_off,
                 JC_OFFSETOF(jc_modeframe_v1, previous_tier) ==
                     JC_STRUCT_MODEFRAME_V1_PREVIOUS_TIER_OFF);
JC_STATIC_ASSERT(modeframe_previous_modeflags_off,
                 JC_OFFSETOF(jc_modeframe_v1, previous_modeflags) ==
                     JC_STRUCT_MODEFRAME_V1_PREVIOUS_MODEFLAGS_OFF);
JC_STATIC_ASSERT(modeframe_reserved0_off,
                 JC_OFFSETOF(jc_modeframe_v1, reserved0) ==
                     JC_STRUCT_MODEFRAME_V1_RESERVED0_OFF);
JC_STATIC_ASSERT(modeframe_reserved1_off,
                 JC_OFFSETOF(jc_modeframe_v1, reserved1) ==
                     JC_STRUCT_MODEFRAME_V1_RESERVED1_OFF);
JC_STATIC_ASSERT(modeframe_return_pc_off,
                 JC_OFFSETOF(jc_modeframe_v1, return_pc) ==
                     JC_STRUCT_MODEFRAME_V1_RETURN_PC_OFF);

JC_STATIC_ASSERT(mode_abi_size,
                 sizeof(jc_mode_abi_v1) == JC_STRUCT_MODE_ABI_V1_SIZE);
JC_STATIC_ASSERT(mode_abi_align,
                 JC_ALIGNOF(jc_mode_abi_v1) == JC_STRUCT_MODE_ABI_V1_ALIGN);
JC_STATIC_ASSERT(mode_abi_version_off,
                 JC_OFFSETOF(jc_mode_abi_v1, version) ==
                     JC_STRUCT_MODE_ABI_V1_VERSION_OFF);
JC_STATIC_ASSERT(mode_abi_size_bytes_off,
                 JC_OFFSETOF(jc_mode_abi_v1, size_bytes) ==
                     JC_STRUCT_MODE_ABI_V1_SIZE_BYTES_OFF);
JC_STATIC_ASSERT(mode_abi_target_tier_off,
                 JC_OFFSETOF(jc_mode_abi_v1, target_tier) ==
                     JC_STRUCT_MODE_ABI_V1_TARGET_TIER_OFF);
JC_STATIC_ASSERT(mode_abi_reserved0_off,
                 JC_OFFSETOF(jc_mode_abi_v1, reserved0) ==
                     JC_STRUCT_MODE_ABI_V1_RESERVED0_OFF);
JC_STATIC_ASSERT(mode_abi_flags_off,
                 JC_OFFSETOF(jc_mode_abi_v1, flags) ==
                     JC_STRUCT_MODE_ABI_V1_FLAGS_OFF);
JC_STATIC_ASSERT(mode_abi_entry_vector_off,
                 JC_OFFSETOF(jc_mode_abi_v1, entry_vector) ==
                     JC_STRUCT_MODE_ABI_V1_ENTRY_VECTOR_OFF);
JC_STATIC_ASSERT(mode_abi_return_pc_off,
                 JC_OFFSETOF(jc_mode_abi_v1, return_pc) ==
                     JC_STRUCT_MODE_ABI_V1_RETURN_PC_OFF);
JC_STATIC_ASSERT(mode_abi_error_code_off,
                 JC_OFFSETOF(jc_mode_abi_v1, error_code) ==
                     JC_STRUCT_MODE_ABI_V1_ERROR_CODE_OFF);
JC_STATIC_ASSERT(mode_abi_reserved1_off,
                 JC_OFFSETOF(jc_mode_abi_v1, reserved1) ==
                     JC_STRUCT_MODE_ABI_V1_RESERVED1_OFF);

JC_STATIC_ASSERT(capset_size,
                 sizeof(jc_capset_v1) == JC_STRUCT_CAPSET_V1_SIZE);
JC_STATIC_ASSERT(capset_align,
                 JC_ALIGNOF(jc_capset_v1) == JC_STRUCT_CAPSET_V1_ALIGN);
JC_STATIC_ASSERT(capset_signature_off,
                 JC_OFFSETOF(jc_capset_v1, signature) ==
                     JC_STRUCT_CAPSET_V1_SIGNATURE_OFF);
JC_STATIC_ASSERT(capset_version_off,
                 JC_OFFSETOF(jc_capset_v1, version) ==
                     JC_STRUCT_CAPSET_V1_VERSION_OFF);
JC_STATIC_ASSERT(capset_size_bytes_off,
                 JC_OFFSETOF(jc_capset_v1, size_bytes) ==
                     JC_STRUCT_CAPSET_V1_SIZE_BYTES_OFF);
JC_STATIC_ASSERT(capset_cpu_ladder_id_off,
                 JC_OFFSETOF(jc_capset_v1, cpu_ladder_id) ==
                     JC_STRUCT_CAPSET_V1_CPU_LADDER_ID_OFF);
JC_STATIC_ASSERT(capset_fpu_ladder_id_off,
                 JC_OFFSETOF(jc_capset_v1, fpu_ladder_id) ==
                     JC_STRUCT_CAPSET_V1_FPU_LADDER_ID_OFF);
JC_STATIC_ASSERT(capset_presented_cpu_tier_off,
                 JC_OFFSETOF(jc_capset_v1, presented_cpu_tier) ==
                     JC_STRUCT_CAPSET_V1_PRESENTED_CPU_TIER_OFF);
JC_STATIC_ASSERT(capset_presented_fpu_tier_off,
                 JC_OFFSETOF(jc_capset_v1, presented_fpu_tier) ==
                     JC_STRUCT_CAPSET_V1_PRESENTED_FPU_TIER_OFF);
JC_STATIC_ASSERT(capset_profile_id_off,
                 JC_OFFSETOF(jc_capset_v1, profile_id) ==
                     JC_STRUCT_CAPSET_V1_PROFILE_ID_OFF);
JC_STATIC_ASSERT(capset_reserved0_off,
                 JC_OFFSETOF(jc_capset_v1, reserved0) ==
                     JC_STRUCT_CAPSET_V1_RESERVED0_OFF);
JC_STATIC_ASSERT(capset_cpu_features_off,
                 JC_OFFSETOF(jc_capset_v1, cpu_features) ==
                     JC_STRUCT_CAPSET_V1_CPU_FEATURES_OFF);
JC_STATIC_ASSERT(capset_fpu_features_off,
                 JC_OFFSETOF(jc_capset_v1, fpu_features) ==
                     JC_STRUCT_CAPSET_V1_FPU_FEATURES_OFF);
JC_STATIC_ASSERT(capset_periph_features_off,
                 JC_OFFSETOF(jc_capset_v1, periph_features) ==
                     JC_STRUCT_CAPSET_V1_PERIPH_FEATURES_OFF);
JC_STATIC_ASSERT(capset_topology_ptr_off,
                 JC_OFFSETOF(jc_capset_v1, topology_table_ptr) ==
                     JC_STRUCT_CAPSET_V1_TOPOLOGY_TABLE_PTR_OFF);
JC_STATIC_ASSERT(capset_bdt_ptr_off,
                 JC_OFFSETOF(jc_capset_v1, bdt_ptr) ==
                     JC_STRUCT_CAPSET_V1_BDT_PTR_OFF);
JC_STATIC_ASSERT(capset_limits_ptr_off,
                 JC_OFFSETOF(jc_capset_v1, limits_table_ptr) ==
                     JC_STRUCT_CAPSET_V1_LIMITS_TABLE_PTR_OFF);
JC_STATIC_ASSERT(capset_mem_region_ptr_off,
                 JC_OFFSETOF(jc_capset_v1, mem_region_table_ptr) ==
                     JC_STRUCT_CAPSET_V1_MEM_REGION_TABLE_PTR_OFF);
JC_STATIC_ASSERT(capset_tier_host_ptr_off,
                 JC_OFFSETOF(jc_capset_v1, tier_host_table_ptr) ==
                     JC_STRUCT_CAPSET_V1_TIER_HOST_TABLE_PTR_OFF);
JC_STATIC_ASSERT(capset_max_devices_off,
                 JC_OFFSETOF(jc_capset_v1, max_devices) ==
                     JC_STRUCT_CAPSET_V1_MAX_DEVICES_OFF);
JC_STATIC_ASSERT(capset_max_dma_segments_off,
                 JC_OFFSETOF(jc_capset_v1, max_dma_segments) ==
                     JC_STRUCT_CAPSET_V1_MAX_DMA_SEGMENTS_OFF);
JC_STATIC_ASSERT(capset_max_bdt_entries_off,
                 JC_OFFSETOF(jc_capset_v1, max_bdt_entries) ==
                     JC_STRUCT_CAPSET_V1_MAX_BDT_ENTRIES_OFF);
JC_STATIC_ASSERT(capset_max_irq_routes_off,
                 JC_OFFSETOF(jc_capset_v1, max_irq_routes) ==
                     JC_STRUCT_CAPSET_V1_MAX_IRQ_ROUTES_OFF);
JC_STATIC_ASSERT(capset_reserved1_off,
                 JC_OFFSETOF(jc_capset_v1, reserved1) ==
                     JC_STRUCT_CAPSET_V1_RESERVED1_OFF);
JC_STATIC_ASSERT(capset_reserved2_off,
                 JC_OFFSETOF(jc_capset_v1, reserved2) ==
                     JC_STRUCT_CAPSET_V1_RESERVED2_OFF);

JC_STATIC_ASSERT(topology_header_size,
                 sizeof(jc_topology_header_v1) ==
                     JC_STRUCT_TOPOLOGY_HEADER_V1_SIZE);
JC_STATIC_ASSERT(topology_header_align,
                 JC_ALIGNOF(jc_topology_header_v1) ==
                     JC_STRUCT_TOPOLOGY_HEADER_V1_ALIGN);
JC_STATIC_ASSERT(topology_header_signature_off,
                 JC_OFFSETOF(jc_topology_header_v1, signature) ==
                     JC_STRUCT_TOPOLOGY_HEADER_V1_SIGNATURE_OFF);
JC_STATIC_ASSERT(topology_header_version_off,
                 JC_OFFSETOF(jc_topology_header_v1, header_version) ==
                     JC_STRUCT_TOPOLOGY_HEADER_V1_HEADER_VERSION_OFF);
JC_STATIC_ASSERT(topology_header_size_off,
                 JC_OFFSETOF(jc_topology_header_v1, header_size) ==
                     JC_STRUCT_TOPOLOGY_HEADER_V1_HEADER_SIZE_OFF);
JC_STATIC_ASSERT(topology_header_entry_size_off,
                 JC_OFFSETOF(jc_topology_header_v1, entry_size) ==
                     JC_STRUCT_TOPOLOGY_HEADER_V1_ENTRY_SIZE_OFF);
JC_STATIC_ASSERT(topology_header_entry_count_off,
                 JC_OFFSETOF(jc_topology_header_v1, entry_count) ==
                     JC_STRUCT_TOPOLOGY_HEADER_V1_ENTRY_COUNT_OFF);
JC_STATIC_ASSERT(topology_header_total_size_off,
                 JC_OFFSETOF(jc_topology_header_v1, total_size) ==
                     JC_STRUCT_TOPOLOGY_HEADER_V1_TOTAL_SIZE_OFF);

JC_STATIC_ASSERT(topology_entry_size,
                 sizeof(jc_topology_entry_v1) ==
                     JC_STRUCT_TOPOLOGY_ENTRY_V1_SIZE);
JC_STATIC_ASSERT(topology_entry_align,
                 JC_ALIGNOF(jc_topology_entry_v1) ==
                     JC_STRUCT_TOPOLOGY_ENTRY_V1_ALIGN);
JC_STATIC_ASSERT(topology_entry_socket_id_off,
                 JC_OFFSETOF(jc_topology_entry_v1, socket_id) ==
                     JC_STRUCT_TOPOLOGY_ENTRY_V1_SOCKET_ID_OFF);
JC_STATIC_ASSERT(topology_entry_cluster_id_off,
                 JC_OFFSETOF(jc_topology_entry_v1, cluster_id) ==
                     JC_STRUCT_TOPOLOGY_ENTRY_V1_CLUSTER_ID_OFF);
JC_STATIC_ASSERT(topology_entry_core_id_off,
                 JC_OFFSETOF(jc_topology_entry_v1, core_id) ==
                     JC_STRUCT_TOPOLOGY_ENTRY_V1_CORE_ID_OFF);
JC_STATIC_ASSERT(topology_entry_thread_id_off,
                 JC_OFFSETOF(jc_topology_entry_v1, thread_id) ==
                     JC_STRUCT_TOPOLOGY_ENTRY_V1_THREAD_ID_OFF);
JC_STATIC_ASSERT(topology_entry_cache_l1_id_off,
                 JC_OFFSETOF(jc_topology_entry_v1, cache_l1_id) ==
                     JC_STRUCT_TOPOLOGY_ENTRY_V1_CACHE_L1_ID_OFF);
JC_STATIC_ASSERT(topology_entry_cache_l2_id_off,
                 JC_OFFSETOF(jc_topology_entry_v1, cache_l2_id) ==
                     JC_STRUCT_TOPOLOGY_ENTRY_V1_CACHE_L2_ID_OFF);
JC_STATIC_ASSERT(topology_entry_cache_l3_id_off,
                 JC_OFFSETOF(jc_topology_entry_v1, cache_l3_id) ==
                     JC_STRUCT_TOPOLOGY_ENTRY_V1_CACHE_L3_ID_OFF);
JC_STATIC_ASSERT(topology_entry_coherence_domain_id_off,
                 JC_OFFSETOF(jc_topology_entry_v1, coherence_domain_id) ==
                     JC_STRUCT_TOPOLOGY_ENTRY_V1_COHERENCE_DOMAIN_ID_OFF);
JC_STATIC_ASSERT(topology_entry_numa_node_id_off,
                 JC_OFFSETOF(jc_topology_entry_v1, numa_node_id) ==
                     JC_STRUCT_TOPOLOGY_ENTRY_V1_NUMA_NODE_ID_OFF);
JC_STATIC_ASSERT(topology_entry_reserved0_off,
                 JC_OFFSETOF(jc_topology_entry_v1, reserved0) ==
                     JC_STRUCT_TOPOLOGY_ENTRY_V1_RESERVED0_OFF);

JC_STATIC_ASSERT(tier_host_header_size,
                 sizeof(jc_tier_host_header_v1) ==
                     JC_STRUCT_TIER_HOST_HEADER_V1_SIZE);
JC_STATIC_ASSERT(tier_host_header_align,
                 JC_ALIGNOF(jc_tier_host_header_v1) ==
                     JC_STRUCT_TIER_HOST_HEADER_V1_ALIGN);
JC_STATIC_ASSERT(tier_host_header_signature_off,
                 JC_OFFSETOF(jc_tier_host_header_v1, signature) ==
                     JC_STRUCT_TIER_HOST_HEADER_V1_SIGNATURE_OFF);
JC_STATIC_ASSERT(tier_host_header_version_off,
                 JC_OFFSETOF(jc_tier_host_header_v1, header_version) ==
                     JC_STRUCT_TIER_HOST_HEADER_V1_HEADER_VERSION_OFF);
JC_STATIC_ASSERT(tier_host_header_size_off,
                 JC_OFFSETOF(jc_tier_host_header_v1, header_size) ==
                     JC_STRUCT_TIER_HOST_HEADER_V1_HEADER_SIZE_OFF);
JC_STATIC_ASSERT(tier_host_header_entry_size_off,
                 JC_OFFSETOF(jc_tier_host_header_v1, entry_size) ==
                     JC_STRUCT_TIER_HOST_HEADER_V1_ENTRY_SIZE_OFF);
JC_STATIC_ASSERT(tier_host_header_entry_count_off,
                 JC_OFFSETOF(jc_tier_host_header_v1, entry_count) ==
                     JC_STRUCT_TIER_HOST_HEADER_V1_ENTRY_COUNT_OFF);
JC_STATIC_ASSERT(tier_host_header_total_size_off,
                 JC_OFFSETOF(jc_tier_host_header_v1, total_size) ==
                     JC_STRUCT_TIER_HOST_HEADER_V1_TOTAL_SIZE_OFF);

JC_STATIC_ASSERT(tier_host_entry_size,
                 sizeof(jc_tier_host_entry_v1) ==
                     JC_STRUCT_TIER_HOST_ENTRY_V1_SIZE);
JC_STATIC_ASSERT(tier_host_entry_align,
                 JC_ALIGNOF(jc_tier_host_entry_v1) ==
                     JC_STRUCT_TIER_HOST_ENTRY_V1_ALIGN);
JC_STATIC_ASSERT(tier_host_entry_socket_id_off,
                 JC_OFFSETOF(jc_tier_host_entry_v1, socket_id) ==
                     JC_STRUCT_TIER_HOST_ENTRY_V1_SOCKET_ID_OFF);
JC_STATIC_ASSERT(tier_host_entry_cluster_id_off,
                 JC_OFFSETOF(jc_tier_host_entry_v1, cluster_id) ==
                     JC_STRUCT_TIER_HOST_ENTRY_V1_CLUSTER_ID_OFF);
JC_STATIC_ASSERT(tier_host_entry_core_id_off,
                 JC_OFFSETOF(jc_tier_host_entry_v1, core_id) ==
                     JC_STRUCT_TIER_HOST_ENTRY_V1_CORE_ID_OFF);
JC_STATIC_ASSERT(tier_host_entry_reserved0_off,
                 JC_OFFSETOF(jc_tier_host_entry_v1, reserved0) ==
                     JC_STRUCT_TIER_HOST_ENTRY_V1_RESERVED0_OFF);
JC_STATIC_ASSERT(tier_host_entry_tier_mask_off,
                 JC_OFFSETOF(jc_tier_host_entry_v1, tier_mask) ==
                     JC_STRUCT_TIER_HOST_ENTRY_V1_TIER_MASK_OFF);
JC_STATIC_ASSERT(tier_host_entry_reserved1_off,
                 JC_OFFSETOF(jc_tier_host_entry_v1, reserved1) ==
                     JC_STRUCT_TIER_HOST_ENTRY_V1_RESERVED1_OFF);
JC_STATIC_ASSERT(tier_host_entry_reserved2_off,
                 JC_OFFSETOF(jc_tier_host_entry_v1, reserved2) ==
                     JC_STRUCT_TIER_HOST_ENTRY_V1_RESERVED2_OFF);

JC_STATIC_ASSERT(mem_region_header_size,
                 sizeof(jc_mem_region_header_v1) ==
                     JC_STRUCT_MEM_REGION_HEADER_V1_SIZE);
JC_STATIC_ASSERT(mem_region_header_align,
                 JC_ALIGNOF(jc_mem_region_header_v1) ==
                     JC_STRUCT_MEM_REGION_HEADER_V1_ALIGN);
JC_STATIC_ASSERT(mem_region_header_signature_off,
                 JC_OFFSETOF(jc_mem_region_header_v1, signature) ==
                     JC_STRUCT_MEM_REGION_HEADER_V1_SIGNATURE_OFF);
JC_STATIC_ASSERT(mem_region_header_version_off,
                 JC_OFFSETOF(jc_mem_region_header_v1, header_version) ==
                     JC_STRUCT_MEM_REGION_HEADER_V1_HEADER_VERSION_OFF);
JC_STATIC_ASSERT(mem_region_header_size_off,
                 JC_OFFSETOF(jc_mem_region_header_v1, header_size) ==
                     JC_STRUCT_MEM_REGION_HEADER_V1_HEADER_SIZE_OFF);
JC_STATIC_ASSERT(mem_region_header_entry_size_off,
                 JC_OFFSETOF(jc_mem_region_header_v1, entry_size) ==
                     JC_STRUCT_MEM_REGION_HEADER_V1_ENTRY_SIZE_OFF);
JC_STATIC_ASSERT(mem_region_header_entry_count_off,
                 JC_OFFSETOF(jc_mem_region_header_v1, entry_count) ==
                     JC_STRUCT_MEM_REGION_HEADER_V1_ENTRY_COUNT_OFF);
JC_STATIC_ASSERT(mem_region_header_total_size_off,
                 JC_OFFSETOF(jc_mem_region_header_v1, total_size) ==
                     JC_STRUCT_MEM_REGION_HEADER_V1_TOTAL_SIZE_OFF);

JC_STATIC_ASSERT(mem_region_entry_size,
                 sizeof(jc_mem_region_entry_v1) ==
                     JC_STRUCT_MEM_REGION_ENTRY_V1_SIZE);
JC_STATIC_ASSERT(mem_region_entry_align,
                 JC_ALIGNOF(jc_mem_region_entry_v1) ==
                     JC_STRUCT_MEM_REGION_ENTRY_V1_ALIGN);
JC_STATIC_ASSERT(mem_region_entry_region_kind_off,
                 JC_OFFSETOF(jc_mem_region_entry_v1, region_kind) ==
                     JC_STRUCT_MEM_REGION_ENTRY_V1_REGION_KIND_OFF);
JC_STATIC_ASSERT(mem_region_entry_region_attrs_off,
                 JC_OFFSETOF(jc_mem_region_entry_v1, region_attrs) ==
                     JC_STRUCT_MEM_REGION_ENTRY_V1_REGION_ATTRS_OFF);
JC_STATIC_ASSERT(mem_region_entry_reserved0_off,
                 JC_OFFSETOF(jc_mem_region_entry_v1, reserved0) ==
                     JC_STRUCT_MEM_REGION_ENTRY_V1_RESERVED0_OFF);
JC_STATIC_ASSERT(mem_region_entry_base_addr_off,
                 JC_OFFSETOF(jc_mem_region_entry_v1, base_addr) ==
                     JC_STRUCT_MEM_REGION_ENTRY_V1_BASE_ADDR_OFF);
JC_STATIC_ASSERT(mem_region_entry_size_bytes_off,
                 JC_OFFSETOF(jc_mem_region_entry_v1, size_bytes) ==
                     JC_STRUCT_MEM_REGION_ENTRY_V1_SIZE_BYTES_OFF);
JC_STATIC_ASSERT(mem_region_entry_reserved1_off,
                 JC_OFFSETOF(jc_mem_region_entry_v1, reserved1) ==
                     JC_STRUCT_MEM_REGION_ENTRY_V1_RESERVED1_OFF);

JC_STATIC_ASSERT(bdt_header_size,
                 sizeof(jc_bdt_header_v1) == JC_STRUCT_BDT_HEADER_V1_SIZE);
JC_STATIC_ASSERT(bdt_header_align,
                 JC_ALIGNOF(jc_bdt_header_v1) == JC_STRUCT_BDT_HEADER_V1_ALIGN);
JC_STATIC_ASSERT(bdt_header_signature_off,
                 JC_OFFSETOF(jc_bdt_header_v1, signature) ==
                     JC_STRUCT_BDT_HEADER_V1_SIGNATURE_OFF);
JC_STATIC_ASSERT(bdt_header_version_off,
                 JC_OFFSETOF(jc_bdt_header_v1, header_version) ==
                     JC_STRUCT_BDT_HEADER_V1_HEADER_VERSION_OFF);
JC_STATIC_ASSERT(bdt_header_size_off,
                 JC_OFFSETOF(jc_bdt_header_v1, header_size) ==
                     JC_STRUCT_BDT_HEADER_V1_HEADER_SIZE_OFF);
JC_STATIC_ASSERT(bdt_header_entry_size_off,
                 JC_OFFSETOF(jc_bdt_header_v1, entry_size) ==
                     JC_STRUCT_BDT_HEADER_V1_ENTRY_SIZE_OFF);
JC_STATIC_ASSERT(bdt_header_entry_count_off,
                 JC_OFFSETOF(jc_bdt_header_v1, entry_count) ==
                     JC_STRUCT_BDT_HEADER_V1_ENTRY_COUNT_OFF);
JC_STATIC_ASSERT(bdt_header_total_size_off,
                 JC_OFFSETOF(jc_bdt_header_v1, total_size) ==
                     JC_STRUCT_BDT_HEADER_V1_TOTAL_SIZE_OFF);

JC_STATIC_ASSERT(bdt_entry_size,
                 sizeof(jc_bdt_entry_v1) == JC_STRUCT_BDT_ENTRY_V1_SIZE);
JC_STATIC_ASSERT(bdt_entry_align,
                 JC_ALIGNOF(jc_bdt_entry_v1) == JC_STRUCT_BDT_ENTRY_V1_ALIGN);
JC_STATIC_ASSERT(bdt_entry_desc_version_off,
                 JC_OFFSETOF(jc_bdt_entry_v1, desc_version) ==
                     JC_STRUCT_BDT_ENTRY_V1_DESC_VERSION_OFF);
JC_STATIC_ASSERT(bdt_entry_desc_size_bytes_off,
                 JC_OFFSETOF(jc_bdt_entry_v1, desc_size_bytes) ==
                     JC_STRUCT_BDT_ENTRY_V1_DESC_SIZE_BYTES_OFF);
JC_STATIC_ASSERT(bdt_entry_class_id_off,
                 JC_OFFSETOF(jc_bdt_entry_v1, class_id) ==
                     JC_STRUCT_BDT_ENTRY_V1_CLASS_ID_OFF);
JC_STATIC_ASSERT(bdt_entry_subclass_id_off,
                 JC_OFFSETOF(jc_bdt_entry_v1, subclass_id) ==
                     JC_STRUCT_BDT_ENTRY_V1_SUBCLASS_ID_OFF);
JC_STATIC_ASSERT(bdt_entry_instance_id_off,
                 JC_OFFSETOF(jc_bdt_entry_v1, instance_id) ==
                     JC_STRUCT_BDT_ENTRY_V1_INSTANCE_ID_OFF);
JC_STATIC_ASSERT(bdt_entry_device_version_off,
                 JC_OFFSETOF(jc_bdt_entry_v1, device_version) ==
                     JC_STRUCT_BDT_ENTRY_V1_DEVICE_VERSION_OFF);
JC_STATIC_ASSERT(bdt_entry_caps0_off,
                 JC_OFFSETOF(jc_bdt_entry_v1, caps0) ==
                     JC_STRUCT_BDT_ENTRY_V1_CAPS0_OFF);
JC_STATIC_ASSERT(bdt_entry_caps1_off,
                 JC_OFFSETOF(jc_bdt_entry_v1, caps1) ==
                     JC_STRUCT_BDT_ENTRY_V1_CAPS1_OFF);
JC_STATIC_ASSERT(bdt_entry_irq_route_offset_off,
                 JC_OFFSETOF(jc_bdt_entry_v1, irq_route_offset) ==
                     JC_STRUCT_BDT_ENTRY_V1_IRQ_ROUTE_OFFSET_OFF);
JC_STATIC_ASSERT(bdt_entry_irq_route_count_off,
                 JC_OFFSETOF(jc_bdt_entry_v1, irq_route_count) ==
                     JC_STRUCT_BDT_ENTRY_V1_IRQ_ROUTE_COUNT_OFF);
JC_STATIC_ASSERT(bdt_entry_mmio_base_off,
                 JC_OFFSETOF(jc_bdt_entry_v1, mmio_base) ==
                     JC_STRUCT_BDT_ENTRY_V1_MMIO_BASE_OFF);
JC_STATIC_ASSERT(bdt_entry_mmio_size_off,
                 JC_OFFSETOF(jc_bdt_entry_v1, mmio_size) ==
                     JC_STRUCT_BDT_ENTRY_V1_MMIO_SIZE_OFF);
JC_STATIC_ASSERT(bdt_entry_io_port_base_off,
                 JC_OFFSETOF(jc_bdt_entry_v1, io_port_base) ==
                     JC_STRUCT_BDT_ENTRY_V1_IO_PORT_BASE_OFF);
JC_STATIC_ASSERT(bdt_entry_io_port_size_off,
                 JC_OFFSETOF(jc_bdt_entry_v1, io_port_size) ==
                     JC_STRUCT_BDT_ENTRY_V1_IO_PORT_SIZE_OFF);
JC_STATIC_ASSERT(bdt_entry_block_sector_size_off,
                 JC_OFFSETOF(jc_bdt_entry_v1, block_sector_size) ==
                     JC_STRUCT_BDT_ENTRY_V1_BLOCK_SECTOR_SIZE_OFF);
JC_STATIC_ASSERT(bdt_entry_cai_queue_count_off,
                 JC_OFFSETOF(jc_bdt_entry_v1, cai_queue_count) ==
                     JC_STRUCT_BDT_ENTRY_V1_CAI_QUEUE_COUNT_OFF);
JC_STATIC_ASSERT(bdt_entry_cai_doorbell_offset_off,
                 JC_OFFSETOF(jc_bdt_entry_v1, cai_doorbell_offset) ==
                     JC_STRUCT_BDT_ENTRY_V1_CAI_DOORBELL_OFFSET_OFF);
JC_STATIC_ASSERT(bdt_entry_aux_ptr_off,
                 JC_OFFSETOF(jc_bdt_entry_v1, aux_ptr) ==
                     JC_STRUCT_BDT_ENTRY_V1_AUX_PTR_OFF);
JC_STATIC_ASSERT(bdt_entry_aux_size_off,
                 JC_OFFSETOF(jc_bdt_entry_v1, aux_size) ==
                     JC_STRUCT_BDT_ENTRY_V1_AUX_SIZE_OFF);
JC_STATIC_ASSERT(bdt_entry_aux_type_off,
                 JC_OFFSETOF(jc_bdt_entry_v1, aux_type) ==
                     JC_STRUCT_BDT_ENTRY_V1_AUX_TYPE_OFF);
JC_STATIC_ASSERT(bdt_entry_reserved0_off,
                 JC_OFFSETOF(jc_bdt_entry_v1, reserved0) ==
                     JC_STRUCT_BDT_ENTRY_V1_RESERVED0_OFF);

JC_STATIC_ASSERT(bdt_irq_route_size,
                 sizeof(jc_bdt_irq_route_v1) ==
                     JC_STRUCT_BDT_IRQ_ROUTE_V1_SIZE);
JC_STATIC_ASSERT(bdt_irq_route_align,
                 JC_ALIGNOF(jc_bdt_irq_route_v1) ==
                     JC_STRUCT_BDT_IRQ_ROUTE_V1_ALIGN);
JC_STATIC_ASSERT(bdt_irq_route_domain_id_off,
                 JC_OFFSETOF(jc_bdt_irq_route_v1, domain_id) ==
                     JC_STRUCT_BDT_IRQ_ROUTE_V1_DOMAIN_ID_OFF);
JC_STATIC_ASSERT(bdt_irq_route_irq_line_off,
                 JC_OFFSETOF(jc_bdt_irq_route_v1, irq_line) ==
                     JC_STRUCT_BDT_IRQ_ROUTE_V1_IRQ_LINE_OFF);
JC_STATIC_ASSERT(bdt_irq_route_flags_off,
                 JC_OFFSETOF(jc_bdt_irq_route_v1, flags) ==
                     JC_STRUCT_BDT_IRQ_ROUTE_V1_FLAGS_OFF);
JC_STATIC_ASSERT(bdt_irq_route_reserved0_off,
                 JC_OFFSETOF(jc_bdt_irq_route_v1, reserved0) ==
                     JC_STRUCT_BDT_IRQ_ROUTE_V1_RESERVED0_OFF);

JC_STATIC_ASSERT(bdt_footer_size,
                 sizeof(jc_bdt_footer_v1) == JC_STRUCT_BDT_FOOTER_V1_SIZE);
JC_STATIC_ASSERT(bdt_footer_align,
                 JC_ALIGNOF(jc_bdt_footer_v1) == JC_STRUCT_BDT_FOOTER_V1_ALIGN);
JC_STATIC_ASSERT(bdt_footer_crc32_off,
                 JC_OFFSETOF(jc_bdt_footer_v1, crc32) ==
                     JC_STRUCT_BDT_FOOTER_V1_CRC32_OFF);

JC_STATIC_ASSERT(cai_submit_desc_size,
                 sizeof(jc_cai_submit_desc_v1) ==
                     JC_STRUCT_CAI_SUBMIT_DESC_V1_SIZE);
JC_STATIC_ASSERT(cai_submit_desc_align,
                 JC_ALIGNOF(jc_cai_submit_desc_v1) ==
                     JC_STRUCT_CAI_SUBMIT_DESC_V1_ALIGN);
JC_STATIC_ASSERT(cai_submit_desc_desc_version_off,
                 JC_OFFSETOF(jc_cai_submit_desc_v1, desc_version) ==
                     JC_STRUCT_CAI_SUBMIT_DESC_V1_DESC_VERSION_OFF);
JC_STATIC_ASSERT(cai_submit_desc_desc_size_dw_off,
                 JC_OFFSETOF(jc_cai_submit_desc_v1, desc_size_dw) ==
                     JC_STRUCT_CAI_SUBMIT_DESC_V1_DESC_SIZE_DW_OFF);
JC_STATIC_ASSERT(cai_submit_desc_opcode_off,
                 JC_OFFSETOF(jc_cai_submit_desc_v1, opcode) ==
                     JC_STRUCT_CAI_SUBMIT_DESC_V1_OPCODE_OFF);
JC_STATIC_ASSERT(cai_submit_desc_flags_off,
                 JC_OFFSETOF(jc_cai_submit_desc_v1, flags) ==
                     JC_STRUCT_CAI_SUBMIT_DESC_V1_FLAGS_OFF);
JC_STATIC_ASSERT(cai_submit_desc_context_id_off,
                 JC_OFFSETOF(jc_cai_submit_desc_v1, context_id) ==
                     JC_STRUCT_CAI_SUBMIT_DESC_V1_CONTEXT_ID_OFF);
JC_STATIC_ASSERT(cai_submit_desc_operand_count_off,
                 JC_OFFSETOF(jc_cai_submit_desc_v1, operand_count) ==
                     JC_STRUCT_CAI_SUBMIT_DESC_V1_OPERAND_COUNT_OFF);
JC_STATIC_ASSERT(cai_submit_desc_tag_off,
                 JC_OFFSETOF(jc_cai_submit_desc_v1, tag) ==
                     JC_STRUCT_CAI_SUBMIT_DESC_V1_TAG_OFF);
JC_STATIC_ASSERT(cai_submit_desc_opcode_group_off,
                 JC_OFFSETOF(jc_cai_submit_desc_v1, opcode_group) ==
                     JC_STRUCT_CAI_SUBMIT_DESC_V1_OPCODE_GROUP_OFF);
JC_STATIC_ASSERT(cai_submit_desc_format_primary_off,
                 JC_OFFSETOF(jc_cai_submit_desc_v1, format_primary) ==
                     JC_STRUCT_CAI_SUBMIT_DESC_V1_FORMAT_PRIMARY_OFF);
JC_STATIC_ASSERT(cai_submit_desc_format_aux_off,
                 JC_OFFSETOF(jc_cai_submit_desc_v1, format_aux) ==
                     JC_STRUCT_CAI_SUBMIT_DESC_V1_FORMAT_AUX_OFF);
JC_STATIC_ASSERT(cai_submit_desc_format_flags_off,
                 JC_OFFSETOF(jc_cai_submit_desc_v1, format_flags) ==
                     JC_STRUCT_CAI_SUBMIT_DESC_V1_FORMAT_FLAGS_OFF);
JC_STATIC_ASSERT(cai_submit_desc_operands_ptr_off,
                 JC_OFFSETOF(jc_cai_submit_desc_v1, operands_ptr) ==
                     JC_STRUCT_CAI_SUBMIT_DESC_V1_OPERANDS_PTR_OFF);
JC_STATIC_ASSERT(cai_submit_desc_result_ptr_off,
                 JC_OFFSETOF(jc_cai_submit_desc_v1, result_ptr) ==
                     JC_STRUCT_CAI_SUBMIT_DESC_V1_RESULT_PTR_OFF);
JC_STATIC_ASSERT(cai_submit_desc_result_len_off,
                 JC_OFFSETOF(jc_cai_submit_desc_v1, result_len) ==
                     JC_STRUCT_CAI_SUBMIT_DESC_V1_RESULT_LEN_OFF);
JC_STATIC_ASSERT(cai_submit_desc_result_stride_off,
                 JC_OFFSETOF(jc_cai_submit_desc_v1, result_stride) ==
                     JC_STRUCT_CAI_SUBMIT_DESC_V1_RESULT_STRIDE_OFF);
JC_STATIC_ASSERT(cai_submit_desc_tensor_desc_ptr_off,
                 JC_OFFSETOF(jc_cai_submit_desc_v1, tensor_desc_ptr) ==
                     JC_STRUCT_CAI_SUBMIT_DESC_V1_TENSOR_DESC_PTR_OFF);
JC_STATIC_ASSERT(cai_submit_desc_tensor_desc_len_off,
                 JC_OFFSETOF(jc_cai_submit_desc_v1, tensor_desc_len) ==
                     JC_STRUCT_CAI_SUBMIT_DESC_V1_TENSOR_DESC_LEN_OFF);
JC_STATIC_ASSERT(cai_submit_desc_tensor_rank_off,
                 JC_OFFSETOF(jc_cai_submit_desc_v1, tensor_rank) ==
                     JC_STRUCT_CAI_SUBMIT_DESC_V1_TENSOR_RANK_OFF);
JC_STATIC_ASSERT(cai_submit_desc_tensor_desc_flags_off,
                 JC_OFFSETOF(jc_cai_submit_desc_v1, tensor_desc_flags) ==
                     JC_STRUCT_CAI_SUBMIT_DESC_V1_TENSOR_DESC_FLAGS_OFF);
JC_STATIC_ASSERT(cai_submit_desc_reserved2_off,
                 JC_OFFSETOF(jc_cai_submit_desc_v1, reserved2) ==
                     JC_STRUCT_CAI_SUBMIT_DESC_V1_RESERVED2_OFF);

JC_STATIC_ASSERT(cai_operand_desc_size,
                 sizeof(jc_cai_operand_desc_v1) ==
                     JC_STRUCT_CAI_OPERAND_DESC_V1_SIZE);
JC_STATIC_ASSERT(cai_operand_desc_align,
                 JC_ALIGNOF(jc_cai_operand_desc_v1) ==
                     JC_STRUCT_CAI_OPERAND_DESC_V1_ALIGN);
JC_STATIC_ASSERT(cai_operand_desc_ptr_off,
                 JC_OFFSETOF(jc_cai_operand_desc_v1, ptr) ==
                     JC_STRUCT_CAI_OPERAND_DESC_V1_PTR_OFF);
JC_STATIC_ASSERT(cai_operand_desc_len_off,
                 JC_OFFSETOF(jc_cai_operand_desc_v1, len) ==
                     JC_STRUCT_CAI_OPERAND_DESC_V1_LEN_OFF);
JC_STATIC_ASSERT(cai_operand_desc_stride_off,
                 JC_OFFSETOF(jc_cai_operand_desc_v1, stride) ==
                     JC_STRUCT_CAI_OPERAND_DESC_V1_STRIDE_OFF);
JC_STATIC_ASSERT(cai_operand_desc_flags_off,
                 JC_OFFSETOF(jc_cai_operand_desc_v1, flags) ==
                     JC_STRUCT_CAI_OPERAND_DESC_V1_FLAGS_OFF);
JC_STATIC_ASSERT(cai_operand_desc_reserved0_off,
                 JC_OFFSETOF(jc_cai_operand_desc_v1, reserved0) ==
                     JC_STRUCT_CAI_OPERAND_DESC_V1_RESERVED0_OFF);
JC_STATIC_ASSERT(cai_operand_desc_reserved1_off,
                 JC_OFFSETOF(jc_cai_operand_desc_v1, reserved1) ==
                     JC_STRUCT_CAI_OPERAND_DESC_V1_RESERVED1_OFF);

JC_STATIC_ASSERT(cai_tensor_desc_size,
                 sizeof(jc_cai_tensor_desc_v1) ==
                     JC_STRUCT_CAI_TENSOR_DESC_V1_SIZE);
JC_STATIC_ASSERT(cai_tensor_desc_align,
                 JC_ALIGNOF(jc_cai_tensor_desc_v1) ==
                     JC_STRUCT_CAI_TENSOR_DESC_V1_ALIGN);
JC_STATIC_ASSERT(cai_tensor_desc_desc_version_off,
                 JC_OFFSETOF(jc_cai_tensor_desc_v1, desc_version) ==
                     JC_STRUCT_CAI_TENSOR_DESC_V1_DESC_VERSION_OFF);
JC_STATIC_ASSERT(cai_tensor_desc_desc_size_dw_off,
                 JC_OFFSETOF(jc_cai_tensor_desc_v1, desc_size_dw) ==
                     JC_STRUCT_CAI_TENSOR_DESC_V1_DESC_SIZE_DW_OFF);
JC_STATIC_ASSERT(cai_tensor_desc_rank_off,
                 JC_OFFSETOF(jc_cai_tensor_desc_v1, rank) ==
                     JC_STRUCT_CAI_TENSOR_DESC_V1_RANK_OFF);
JC_STATIC_ASSERT(cai_tensor_desc_elem_format_off,
                 JC_OFFSETOF(jc_cai_tensor_desc_v1, elem_format) ==
                     JC_STRUCT_CAI_TENSOR_DESC_V1_ELEM_FORMAT_OFF);
JC_STATIC_ASSERT(cai_tensor_desc_reserved0_off,
                 JC_OFFSETOF(jc_cai_tensor_desc_v1, reserved0) ==
                     JC_STRUCT_CAI_TENSOR_DESC_V1_RESERVED0_OFF);
JC_STATIC_ASSERT(cai_tensor_desc_flags_off,
                 JC_OFFSETOF(jc_cai_tensor_desc_v1, flags) ==
                     JC_STRUCT_CAI_TENSOR_DESC_V1_FLAGS_OFF);
JC_STATIC_ASSERT(cai_tensor_desc_shape0_off,
                 JC_OFFSETOF(jc_cai_tensor_desc_v1, shape0) ==
                     JC_STRUCT_CAI_TENSOR_DESC_V1_SHAPE0_OFF);
JC_STATIC_ASSERT(cai_tensor_desc_shape1_off,
                 JC_OFFSETOF(jc_cai_tensor_desc_v1, shape1) ==
                     JC_STRUCT_CAI_TENSOR_DESC_V1_SHAPE1_OFF);
JC_STATIC_ASSERT(cai_tensor_desc_shape2_off,
                 JC_OFFSETOF(jc_cai_tensor_desc_v1, shape2) ==
                     JC_STRUCT_CAI_TENSOR_DESC_V1_SHAPE2_OFF);
JC_STATIC_ASSERT(cai_tensor_desc_shape3_off,
                 JC_OFFSETOF(jc_cai_tensor_desc_v1, shape3) ==
                     JC_STRUCT_CAI_TENSOR_DESC_V1_SHAPE3_OFF);
JC_STATIC_ASSERT(cai_tensor_desc_stride0_off,
                 JC_OFFSETOF(jc_cai_tensor_desc_v1, stride0) ==
                     JC_STRUCT_CAI_TENSOR_DESC_V1_STRIDE0_OFF);
JC_STATIC_ASSERT(cai_tensor_desc_stride1_off,
                 JC_OFFSETOF(jc_cai_tensor_desc_v1, stride1) ==
                     JC_STRUCT_CAI_TENSOR_DESC_V1_STRIDE1_OFF);
JC_STATIC_ASSERT(cai_tensor_desc_stride2_off,
                 JC_OFFSETOF(jc_cai_tensor_desc_v1, stride2) ==
                     JC_STRUCT_CAI_TENSOR_DESC_V1_STRIDE2_OFF);
JC_STATIC_ASSERT(cai_tensor_desc_stride3_off,
                 JC_OFFSETOF(jc_cai_tensor_desc_v1, stride3) ==
                     JC_STRUCT_CAI_TENSOR_DESC_V1_STRIDE3_OFF);
JC_STATIC_ASSERT(cai_tensor_desc_reserved1_off,
                 JC_OFFSETOF(jc_cai_tensor_desc_v1, reserved1) ==
                     JC_STRUCT_CAI_TENSOR_DESC_V1_RESERVED1_OFF);
JC_STATIC_ASSERT(cai_tensor_desc_reserved2_off,
                 JC_OFFSETOF(jc_cai_tensor_desc_v1, reserved2) ==
                     JC_STRUCT_CAI_TENSOR_DESC_V1_RESERVED2_OFF);
JC_STATIC_ASSERT(cai_tensor_desc_reserved3_off,
                 JC_OFFSETOF(jc_cai_tensor_desc_v1, reserved3) ==
                     JC_STRUCT_CAI_TENSOR_DESC_V1_RESERVED3_OFF);

JC_STATIC_ASSERT(cai_comp_rec_size,
                 sizeof(jc_cai_comp_rec_v1) ==
                     JC_STRUCT_CAI_COMP_REC_V1_SIZE);
JC_STATIC_ASSERT(cai_comp_rec_align,
                 JC_ALIGNOF(jc_cai_comp_rec_v1) ==
                     JC_STRUCT_CAI_COMP_REC_V1_ALIGN);
JC_STATIC_ASSERT(cai_comp_rec_tag_off,
                 JC_OFFSETOF(jc_cai_comp_rec_v1, tag) ==
                     JC_STRUCT_CAI_COMP_REC_V1_TAG_OFF);
JC_STATIC_ASSERT(cai_comp_rec_status_off,
                 JC_OFFSETOF(jc_cai_comp_rec_v1, status) ==
                     JC_STRUCT_CAI_COMP_REC_V1_STATUS_OFF);
JC_STATIC_ASSERT(cai_comp_rec_ext_status_off,
                 JC_OFFSETOF(jc_cai_comp_rec_v1, ext_status) ==
                     JC_STRUCT_CAI_COMP_REC_V1_EXT_STATUS_OFF);
JC_STATIC_ASSERT(cai_comp_rec_bytes_written_off,
                 JC_OFFSETOF(jc_cai_comp_rec_v1, bytes_written) ==
                     JC_STRUCT_CAI_COMP_REC_V1_BYTES_WRITTEN_OFF);
JC_STATIC_ASSERT(cai_comp_rec_reserved0_off,
                 JC_OFFSETOF(jc_cai_comp_rec_v1, reserved0) ==
                     JC_STRUCT_CAI_COMP_REC_V1_RESERVED0_OFF);

JC_STATIC_ASSERT(jcom_header_size,
                 sizeof(jc_jcom_header_v1) == JC_STRUCT_JCOM_HEADER_V1_SIZE);
JC_STATIC_ASSERT(jcom_header_align,
                 JC_ALIGNOF(jc_jcom_header_v1) == JC_STRUCT_JCOM_HEADER_V1_ALIGN);
JC_STATIC_ASSERT(jcom_header_signature_off,
                 JC_OFFSETOF(jc_jcom_header_v1, signature) ==
                     JC_STRUCT_JCOM_HEADER_V1_SIGNATURE_OFF);
JC_STATIC_ASSERT(jcom_header_version_off,
                 JC_OFFSETOF(jc_jcom_header_v1, header_version) ==
                     JC_STRUCT_JCOM_HEADER_V1_HEADER_VERSION_OFF);
JC_STATIC_ASSERT(jcom_header_size_off,
                 JC_OFFSETOF(jc_jcom_header_v1, header_size) ==
                     JC_STRUCT_JCOM_HEADER_V1_HEADER_SIZE_OFF);
JC_STATIC_ASSERT(jcom_header_min_cpu_tier_off,
                 JC_OFFSETOF(jc_jcom_header_v1, min_cpu_tier) ==
                     JC_STRUCT_JCOM_HEADER_V1_MIN_CPU_TIER_OFF);
JC_STATIC_ASSERT(jcom_header_reserved0_off,
                 JC_OFFSETOF(jc_jcom_header_v1, reserved0) ==
                     JC_STRUCT_JCOM_HEADER_V1_RESERVED0_OFF);
JC_STATIC_ASSERT(jcom_header_flags_off,
                 JC_OFFSETOF(jc_jcom_header_v1, flags) ==
                     JC_STRUCT_JCOM_HEADER_V1_FLAGS_OFF);
JC_STATIC_ASSERT(jcom_header_load_policy_off,
                 JC_OFFSETOF(jc_jcom_header_v1, load_policy) ==
                     JC_STRUCT_JCOM_HEADER_V1_LOAD_POLICY_OFF);
JC_STATIC_ASSERT(jcom_header_load_addr_off,
                 JC_OFFSETOF(jc_jcom_header_v1, load_addr) ==
                     JC_STRUCT_JCOM_HEADER_V1_LOAD_ADDR_OFF);
JC_STATIC_ASSERT(jcom_header_entry_offset_off,
                 JC_OFFSETOF(jc_jcom_header_v1, entry_offset) ==
                     JC_STRUCT_JCOM_HEADER_V1_ENTRY_OFFSET_OFF);
JC_STATIC_ASSERT(jcom_header_bss_size_off,
                 JC_OFFSETOF(jc_jcom_header_v1, bss_size) ==
                     JC_STRUCT_JCOM_HEADER_V1_BSS_SIZE_OFF);
JC_STATIC_ASSERT(jcom_header_image_size_off,
                 JC_OFFSETOF(jc_jcom_header_v1, image_size) ==
                     JC_STRUCT_JCOM_HEADER_V1_IMAGE_SIZE_OFF);
JC_STATIC_ASSERT(jcom_header_tlv_size_off,
                 JC_OFFSETOF(jc_jcom_header_v1, tlv_size) ==
                     JC_STRUCT_JCOM_HEADER_V1_TLV_SIZE_OFF);
JC_STATIC_ASSERT(jcom_header_crc32_off,
                 JC_OFFSETOF(jc_jcom_header_v1, crc32) ==
                     JC_STRUCT_JCOM_HEADER_V1_CRC32_OFF);
JC_STATIC_ASSERT(jcom_header_reserved1_off,
                 JC_OFFSETOF(jc_jcom_header_v1, reserved1) ==
                     JC_STRUCT_JCOM_HEADER_V1_RESERVED1_OFF);

JC_STATIC_ASSERT(cpmx_superblock_size,
                 sizeof(jc_cpmx_superblock_v1) ==
                     JC_STRUCT_CPMX_SUPERBLOCK_V1_SIZE);
JC_STATIC_ASSERT(cpmx_superblock_align,
                 JC_ALIGNOF(jc_cpmx_superblock_v1) ==
                     JC_STRUCT_CPMX_SUPERBLOCK_V1_ALIGN);
JC_STATIC_ASSERT(cpmx_superblock_signature_off,
                 JC_OFFSETOF(jc_cpmx_superblock_v1, signature) ==
                     JC_STRUCT_CPMX_SUPERBLOCK_V1_SIGNATURE_OFF);
JC_STATIC_ASSERT(cpmx_superblock_version_off,
                 JC_OFFSETOF(jc_cpmx_superblock_v1, version) ==
                     JC_STRUCT_CPMX_SUPERBLOCK_V1_VERSION_OFF);
JC_STATIC_ASSERT(cpmx_superblock_size_bytes_off,
                 JC_OFFSETOF(jc_cpmx_superblock_v1, size_bytes) ==
                     JC_STRUCT_CPMX_SUPERBLOCK_V1_SIZE_BYTES_OFF);
JC_STATIC_ASSERT(cpmx_superblock_sector_size_off,
                 JC_OFFSETOF(jc_cpmx_superblock_v1, sector_size) ==
                     JC_STRUCT_CPMX_SUPERBLOCK_V1_SECTOR_SIZE_OFF);
JC_STATIC_ASSERT(cpmx_superblock_sectors_per_block_off,
                 JC_OFFSETOF(jc_cpmx_superblock_v1, sectors_per_block) ==
                     JC_STRUCT_CPMX_SUPERBLOCK_V1_SECTORS_PER_BLOCK_OFF);
JC_STATIC_ASSERT(cpmx_superblock_dir_entry_count_off,
                 JC_OFFSETOF(jc_cpmx_superblock_v1, dir_entry_count) ==
                     JC_STRUCT_CPMX_SUPERBLOCK_V1_DIR_ENTRY_COUNT_OFF);
JC_STATIC_ASSERT(cpmx_superblock_reserved0_off,
                 JC_OFFSETOF(jc_cpmx_superblock_v1, reserved0) ==
                     JC_STRUCT_CPMX_SUPERBLOCK_V1_RESERVED0_OFF);
JC_STATIC_ASSERT(cpmx_superblock_total_sectors_off,
                 JC_OFFSETOF(jc_cpmx_superblock_v1, total_sectors) ==
                     JC_STRUCT_CPMX_SUPERBLOCK_V1_TOTAL_SECTORS_OFF);
JC_STATIC_ASSERT(cpmx_superblock_dir_start_lba_off,
                 JC_OFFSETOF(jc_cpmx_superblock_v1, dir_start_lba) ==
                     JC_STRUCT_CPMX_SUPERBLOCK_V1_DIR_START_LBA_OFF);
JC_STATIC_ASSERT(cpmx_superblock_data_start_lba_off,
                 JC_OFFSETOF(jc_cpmx_superblock_v1, data_start_lba) ==
                     JC_STRUCT_CPMX_SUPERBLOCK_V1_DATA_START_LBA_OFF);
JC_STATIC_ASSERT(cpmx_superblock_alloc_block_count_off,
                 JC_OFFSETOF(jc_cpmx_superblock_v1, alloc_block_count) ==
                     JC_STRUCT_CPMX_SUPERBLOCK_V1_ALLOC_BLOCK_COUNT_OFF);
JC_STATIC_ASSERT(cpmx_superblock_volume_id_off,
                 JC_OFFSETOF(jc_cpmx_superblock_v1, volume_id) ==
                     JC_STRUCT_CPMX_SUPERBLOCK_V1_VOLUME_ID_OFF);
JC_STATIC_ASSERT(cpmx_superblock_flags_off,
                 JC_OFFSETOF(jc_cpmx_superblock_v1, flags) ==
                     JC_STRUCT_CPMX_SUPERBLOCK_V1_FLAGS_OFF);
JC_STATIC_ASSERT(cpmx_superblock_crc32_off,
                 JC_OFFSETOF(jc_cpmx_superblock_v1, crc32) ==
                     JC_STRUCT_CPMX_SUPERBLOCK_V1_CRC32_OFF);
JC_STATIC_ASSERT(cpmx_superblock_reserved1_off,
                 JC_OFFSETOF(jc_cpmx_superblock_v1, reserved1) ==
                     JC_STRUCT_CPMX_SUPERBLOCK_V1_RESERVED1_OFF);
JC_STATIC_ASSERT(cpmx_superblock_reserved2_off,
                 JC_OFFSETOF(jc_cpmx_superblock_v1, reserved2) ==
                     JC_STRUCT_CPMX_SUPERBLOCK_V1_RESERVED2_OFF);

JC_STATIC_ASSERT(cpmx_dir_entry_size,
                 sizeof(jc_cpmx_dir_entry_v1) ==
                     JC_STRUCT_CPMX_DIR_ENTRY_V1_SIZE);
JC_STATIC_ASSERT(cpmx_dir_entry_align,
                 JC_ALIGNOF(jc_cpmx_dir_entry_v1) ==
                     JC_STRUCT_CPMX_DIR_ENTRY_V1_ALIGN);
JC_STATIC_ASSERT(cpmx_dir_entry_user_off,
                 JC_OFFSETOF(jc_cpmx_dir_entry_v1, user) ==
                     JC_STRUCT_CPMX_DIR_ENTRY_V1_USER_OFF);
JC_STATIC_ASSERT(cpmx_dir_entry_name_off,
                 JC_OFFSETOF(jc_cpmx_dir_entry_v1, name) ==
                     JC_STRUCT_CPMX_DIR_ENTRY_V1_NAME_OFF);
JC_STATIC_ASSERT(cpmx_dir_entry_ext_off,
                 JC_OFFSETOF(jc_cpmx_dir_entry_v1, ext) ==
                     JC_STRUCT_CPMX_DIR_ENTRY_V1_EXT_OFF);
JC_STATIC_ASSERT(cpmx_dir_entry_flags_off,
                 JC_OFFSETOF(jc_cpmx_dir_entry_v1, flags) ==
                     JC_STRUCT_CPMX_DIR_ENTRY_V1_FLAGS_OFF);
JC_STATIC_ASSERT(cpmx_dir_entry_extent_off,
                 JC_OFFSETOF(jc_cpmx_dir_entry_v1, extent) ==
                     JC_STRUCT_CPMX_DIR_ENTRY_V1_EXTENT_OFF);
JC_STATIC_ASSERT(cpmx_dir_entry_reserved0_off,
                 JC_OFFSETOF(jc_cpmx_dir_entry_v1, reserved0) ==
                     JC_STRUCT_CPMX_DIR_ENTRY_V1_RESERVED0_OFF);
JC_STATIC_ASSERT(cpmx_dir_entry_record_count_off,
                 JC_OFFSETOF(jc_cpmx_dir_entry_v1, record_count) ==
                     JC_STRUCT_CPMX_DIR_ENTRY_V1_RECORD_COUNT_OFF);
JC_STATIC_ASSERT(cpmx_dir_entry_block_ptrs_off,
                 JC_OFFSETOF(jc_cpmx_dir_entry_v1, block_ptrs) ==
                     JC_STRUCT_CPMX_DIR_ENTRY_V1_BLOCK_PTRS_OFF);

#endif /* JC_CONTRACTS_LAYOUT_H */
