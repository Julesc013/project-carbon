#include "jc_bsp.h"
#include "jc_contracts.h"
#include "jc_contracts_autogen.h"
#include "jc_offsets_autogen.h"

const jc_platform_desc_v1 jc_platform_desc = {
    JC_PLATFORM_DESC_V1_SIGNATURE,
    JC_PLATFORM_DESC_V1_VERSION,
    (jc_u16)sizeof(jc_platform_desc_v1),
    JC_PROFILE_SOC_RETRO,
    {0, 0, 0},
    {'H', 'W', '_', 'R', 'E', 'F', '1', 0, 0, 0, 0, 0, 0, 0, 0, 0}};

static const jc_feature_bitmap_v1 jc_cpu_features_hw_ref1 = {0, 0, 0, 0};
static const jc_feature_bitmap_v1 jc_fpu_features_hw_ref1 = {0, 0, 0, 0};
static const jc_feature_bitmap_v1 jc_periph_features_hw_ref1 = {0, 0, 0, 0};
static const jc_limits_table_v1 jc_limits_hw_ref1 = {0, 0, 0, 0, 0, 0, 1, 1, {0, 0, 0}};

typedef struct {
  jc_bdt_header_v1 header;
  jc_bdt_footer_v1 footer;
} jc_bdt_image_v1;

static const jc_bdt_image_v1 jc_bdt_hw_ref1 = {
    {JC_MAGIC_BDT,
     JC_BDT_HEADER_V1_VERSION,
     JC_BDT_HEADER_V1_SIZE,
     JC_BDT_ENTRY_V1_SIZE,
     0,
     (jc_u32)(JC_BDT_HEADER_V1_SIZE + JC_BDT_FOOTER_V1_SIZE)},
    {0xBE00624Bu}};

const jc_discovery_table_v1 jc_discovery_hw_ref1 = {
    JC_MAGIC_DISCOVERY_TABLE,
    JC_DISCOVERY_TABLE_V1_VERSION,
    JC_DISCOVERY_TABLE_V1_SIZE,
    JC_TIER_LADDER_Z80,
    JC_TIER_LADDER_AM95,
    JC_TIER_Z80_P0,
    JC_TIER_AM95_P0,
    JC_PROFILE_SOC_RETRO,
    {0, 0, 0},
    {0, 0},
    {(jc_u32)(unsigned long)&jc_bdt_hw_ref1, 0},
    {(jc_u32)(unsigned long)&jc_limits_hw_ref1, 0},
    {(jc_u32)(unsigned long)&jc_cpu_features_hw_ref1, 0},
    {(jc_u32)(unsigned long)&jc_fpu_features_hw_ref1, 0},
    {(jc_u32)(unsigned long)&jc_periph_features_hw_ref1, 0}};

const jc_bsp_anchor_v1 jc_bsp_anchor_hw_ref1 = {
    JC_MAGIC_BSP_ANCHOR,
    JC_BSP_ANCHOR_V1_VERSION,
    JC_STRUCT_BSP_ANCHOR_V1_SIZE,
    {(jc_u32)(unsigned long)&jc_discovery_hw_ref1, 0},
    {0, 0}};

const jc_u16 jc_bsp_anchor_addr =
    (jc_u16)(unsigned long)&jc_bsp_anchor_hw_ref1;
const jc_u16 jc_bsp_stack_top = 0xF000u;
