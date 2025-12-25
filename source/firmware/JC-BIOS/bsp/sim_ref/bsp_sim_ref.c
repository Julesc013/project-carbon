#include "jc_bsp.h"
#include "jc_contracts.h"
#include "jc_contracts_autogen.h"
#include "jc_offsets_autogen.h"
#include "jc_cai.h"

#ifndef JC_BSP_PROFILE_ID
#define JC_BSP_PROFILE_ID JC_PROFILE_SOC_RETRO
#endif

const jc_platform_desc_v1 jc_platform_desc = {
    JC_PLATFORM_DESC_V1_SIGNATURE,
    JC_PLATFORM_DESC_V1_VERSION,
    (jc_u16)sizeof(jc_platform_desc_v1),
    JC_BSP_PROFILE_ID,
    {0, 0, 0},
    {'S', 'I', 'M', '_', 'R', 'E', 'F', 0, 0, 0, 0, 0, 0, 0, 0, 0}};

static const jc_feature_bitmap_v1 jc_cpu_features_sim_ref = {
    JC_CPU_FEAT_MODE_SWITCH_MASK, 0, 0, 0};

#if defined(JC_SIM_ENABLE_IRQ)
#define JC_SIM_IRQ_CAP_MASK JC_DEV_COMPAT_IRQ_MASK
#else
#define JC_SIM_IRQ_CAP_MASK 0u
#endif

#define JC_SIM_UART_CAPS                                                  \
  (JC_DEV_COMPAT_POLLING_MASK | JC_DEV_COMPAT_MMIO_MASK |                 \
   JC_DEV_COMPAT_WAIT_MASK | JC_SIM_IRQ_CAP_MASK)
#define JC_SIM_PIC_CAPS                                                   \
  (JC_DEV_COMPAT_POLLING_MASK | JC_DEV_COMPAT_MMIO_MASK |                 \
   JC_DEV_COMPAT_WAIT_MASK | JC_SIM_IRQ_CAP_MASK)
#define JC_SIM_TIMER_CAPS1 JC_SIM_IRQ_CAP_MASK
#if defined(JC_SIM_ENABLE_IRQ)
#define JC_SIM_BDT_CRC_NO_CAI 0xCC89BB20u
#define JC_SIM_BDT_CRC_CAI 0xE67F2AF0u
#else
#define JC_SIM_BDT_CRC_NO_CAI 0x342E9E32u
#define JC_SIM_BDT_CRC_CAI 0xDB42A284u
#endif

#if defined(JC_SIM_ENABLE_CAI)
static const jc_feature_bitmap_v1 jc_fpu_features_sim_ref = {
    JC_FPU_FEAT_AM9513_ASYNC_SCALAR_MASK, 0, 0, 0};

static const jc_feature_bitmap_v1 jc_periph_features_sim_ref = {
    JC_PERIPH_FEAT_CAI_MASK | JC_PERIPH_FEAT_BDT_MASK |
        JC_PERIPH_FEAT_DEVICE_MODEL_MASK,
    0,
    0,
    0};
#else
static const jc_feature_bitmap_v1 jc_fpu_features_sim_ref = {0, 0, 0, 0};

static const jc_feature_bitmap_v1 jc_periph_features_sim_ref = {
    JC_PERIPH_FEAT_BDT_MASK | JC_PERIPH_FEAT_DEVICE_MODEL_MASK, 0, 0, 0};
#endif

static const jc_limits_table_v1 jc_limits_sim_ref = {0, 0, 0, 0, 0, 0, 1, 1, {0, 0, 0}};

#if defined(JC_SIM_ENABLE_CAI)
typedef struct {
  jc_bdt_header_v1 header;
  jc_bdt_entry_v1 entries[5];
  jc_bdt_footer_v1 footer;
} jc_bdt_image_v1;

static const jc_bdt_image_v1 jc_bdt_sim_ref = {
    {JC_MAGIC_BDT,
     JC_BDT_HEADER_V1_VERSION,
     JC_BDT_HEADER_V1_SIZE,
     JC_BDT_ENTRY_V1_SIZE,
     5,
     (jc_u32)(JC_BDT_HEADER_V1_SIZE + 5u * JC_BDT_ENTRY_V1_SIZE +
              JC_BDT_FOOTER_V1_SIZE)},
    {{JC_BDT_ENTRY_V1_VERSION,
      JC_BDT_ENTRY_V1_SIZE,
      JC_DEVCLASS_UART,
      0,
      0,
      1,
      JC_SIM_UART_CAPS,
      0,
      0,
      0,
      {0x0000F100u, 0},
      0x00000100u,
      0,
      0,
      0,
      0,
      0,
      0,
      {0, 0},
      0,
      0,
      0},
     {JC_BDT_ENTRY_V1_VERSION,
      JC_BDT_ENTRY_V1_SIZE,
      JC_DEVCLASS_TIMER,
      0,
      0,
      1,
      1000000u,
      JC_SIM_TIMER_CAPS1,
      0,
      0,
      {0x0000F100u, 0},
      0x00000100u,
      0,
      0,
      0,
      0,
      0,
      0,
      {0, 0},
      0,
      0,
      0},
     {JC_BDT_ENTRY_V1_VERSION,
      JC_BDT_ENTRY_V1_SIZE,
      JC_DEVCLASS_PIC,
      0,
      0,
      1,
      JC_SIM_PIC_CAPS,
      0,
      0,
      0,
      {0x0000F100u, 0},
      0x00000100u,
      0,
      0,
      0,
      0,
      0,
      0,
      {0, 0},
      0,
      0,
      0},
     {JC_BDT_ENTRY_V1_VERSION,
      JC_BDT_ENTRY_V1_SIZE,
      JC_DEVCLASS_STORAGE,
      0,
      0,
      1,
      (JC_DEV_COMPAT_POLLING_MASK | JC_DEV_COMPAT_PORT_IO_MASK |
       JC_DEV_COMPAT_WAIT_MASK),
      500000u,
      0,
      0,
      {0, 0},
      0,
      0x000001F0u,
      8,
      512,
      0,
      0,
      {0, 0},
      0,
      0,
      0},
     {JC_BDT_ENTRY_V1_VERSION,
      JC_BDT_ENTRY_V1_SIZE,
      JC_DEVCLASS_ACCEL,
      0,
      0,
      1,
      0,
      0,
      0,
      0,
      {0, 0},
      0,
      0,
      0,
      0,
      1,
      0,
      {0, 0},
      0,
      JC_CAI_AUX_MOCK,
      0}},
    {JC_SIM_BDT_CRC_CAI}};
#else
typedef struct {
  jc_bdt_header_v1 header;
  jc_bdt_entry_v1 entries[4];
  jc_bdt_footer_v1 footer;
} jc_bdt_image_v1;

static const jc_bdt_image_v1 jc_bdt_sim_ref = {
    {JC_MAGIC_BDT,
     JC_BDT_HEADER_V1_VERSION,
     JC_BDT_HEADER_V1_SIZE,
     JC_BDT_ENTRY_V1_SIZE,
     4,
     (jc_u32)(JC_BDT_HEADER_V1_SIZE + 4u * JC_BDT_ENTRY_V1_SIZE +
              JC_BDT_FOOTER_V1_SIZE)},
    {{JC_BDT_ENTRY_V1_VERSION,
      JC_BDT_ENTRY_V1_SIZE,
      JC_DEVCLASS_UART,
      0,
      0,
      1,
      JC_SIM_UART_CAPS,
      0,
      0,
      0,
      {0x0000F100u, 0},
      0x00000100u,
      0,
      0,
      0,
      0,
      0,
      0,
      {0, 0},
      0,
      0,
      0},
     {JC_BDT_ENTRY_V1_VERSION,
      JC_BDT_ENTRY_V1_SIZE,
      JC_DEVCLASS_TIMER,
      0,
      0,
      1,
      1000000u,
      JC_SIM_TIMER_CAPS1,
      0,
      0,
      {0x0000F100u, 0},
      0x00000100u,
      0,
      0,
      0,
      0,
      0,
      0,
      {0, 0},
      0,
      0,
      0},
     {JC_BDT_ENTRY_V1_VERSION,
      JC_BDT_ENTRY_V1_SIZE,
      JC_DEVCLASS_PIC,
      0,
      0,
      1,
      JC_SIM_PIC_CAPS,
      0,
      0,
      0,
      {0x0000F100u, 0},
      0x00000100u,
      0,
      0,
      0,
      0,
      0,
      0,
      {0, 0},
      0,
      0,
      0},
     {JC_BDT_ENTRY_V1_VERSION,
      JC_BDT_ENTRY_V1_SIZE,
      JC_DEVCLASS_STORAGE,
      0,
      0,
      1,
      (JC_DEV_COMPAT_POLLING_MASK | JC_DEV_COMPAT_PORT_IO_MASK |
       JC_DEV_COMPAT_WAIT_MASK),
      500000u,
      0,
      0,
      {0, 0},
      0,
      0x000001F0u,
      8,
      512,
      0,
      0,
      {0, 0},
      0,
      0,
      0}},
    {JC_SIM_BDT_CRC_NO_CAI}};
#endif

const jc_discovery_table_v1 jc_discovery_sim_ref = {
    JC_MAGIC_DISCOVERY_TABLE,
    JC_DISCOVERY_TABLE_V1_VERSION,
    JC_DISCOVERY_TABLE_V1_SIZE,
    JC_TIER_LADDER_Z80,
    JC_TIER_LADDER_AM95,
    JC_TIER_Z80_P2,
#if defined(JC_SIM_ENABLE_CAI)
    JC_TIER_AM95_P2,
#else
    JC_TIER_AM95_P0,
#endif
    JC_BSP_PROFILE_ID,
    {0, 0, 0},
    {0, 0},
    {(jc_u32)(unsigned long)&jc_bdt_sim_ref, 0},
    {(jc_u32)(unsigned long)&jc_limits_sim_ref, 0},
    {(jc_u32)(unsigned long)&jc_cpu_features_sim_ref, 0},
    {(jc_u32)(unsigned long)&jc_fpu_features_sim_ref, 0},
    {(jc_u32)(unsigned long)&jc_periph_features_sim_ref, 0}};

const jc_bsp_anchor_v1 jc_bsp_anchor_sim_ref = {
    JC_MAGIC_BSP_ANCHOR,
    JC_BSP_ANCHOR_V1_VERSION,
    JC_STRUCT_BSP_ANCHOR_V1_SIZE,
    {(jc_u32)(unsigned long)&jc_discovery_sim_ref, 0},
    {0, 0}};

const jc_u16 jc_bsp_anchor_addr =
    (jc_u16)(unsigned long)&jc_bsp_anchor_sim_ref;
const jc_u16 jc_bsp_stack_top = 0xF000u;
const jc_u16 jc_bsp_tpa_base = 0x0100u;
const jc_u16 jc_bsp_tpa_size = 0x7F00u;
