# Project Carbon — Frozen Architecture Contracts (v1.0)

_GENERATED FILE — DO NOT EDIT._
_Specs: bdt.yaml:v1.0.0, cai.yaml:v1.1.0, csr_map.yaml:v1.0.0, device_model.yaml:v1.0.0, discovery.yaml:v1.1.0, external_if.yaml:v1.0.0, fabric.yaml:v1.1.0, formats.yaml:v1.0.0, interfaces.yaml:v1.0.0, isa_z90.yaml:v1.0.0, memory_attrs.yaml:v1.0.0, mode_switch.yaml:v1.1.0, profiles.yaml:v1.0.0, tiers.yaml:v1.1.0, topology.yaml:v1.0.0._
_Generated: 2025-12-24T09:48:45Z._
_Source: `hdl/tools/gen_specs.py`._

## A) Compatibility Tier Ladders

### Presentation Model

- Name: `presented_tier`
- Description: Reported tier value exposed to software for compatibility decisions.
- Presented tier is reported by discovery, even if internal implementation is a superset.
- Optional or undocumented behaviors are reported via feature bits, not by elevating the tier.
- Reset always starts in P0 for every ladder.
- Tier changes only via MODEUP(target_tier, entry_vector) and RETMD().

### TIER_LADDER_Z80 (Unified 8080-derived compatibility ladder.)

- Reset default: `P0`
- Upgrade rule: `target_tier > current_tier`
- Downgrade rule: `only via RETMD`

| Tier | Value | Label | Strict |
|---:|---:|---|:---:|
| `P0` | `0` | `8080` | true |
| `P1` | `1` | `8085` | true |
| `P2` | `2` | `z80` | true |
| `P3` | `3` | `z180` | true |
| `P4` | `4` | `eZ80 (ADL/24-bit)` | true |
| `P5` | `5` | `z280` | true |
| `P6` | `6` | `z380` | true |
| `P7` | `7` | `z480` | true |

#### Presentation Overrides

| Part | Presents As | Feature Bits | Description |
|---|---|---|---|
| `Z85` | `P2` | `Z85_UNDOC_Z80` | Z85 presents as Z80 (P2) while exposing undocumented Z80 behaviors via feature bits. |
| `Z90` | `P3` | `Z90_Z180_CLASS` | Z90 presents as Z180-compatible (P3). |
| `Z380` | `P6` | `Z380_32BIT_EXTENDED` | Z380 presents as P6 and advertises 32-bit extensions via feature bits. |
| `Z480` | `P7` | `Z480_NATIVE_64` | Z480 presents as P7 and advertises native 64-bit mode via feature bits. |

### TIER_LADDER_AM95 (Am95xx FPU compatibility ladder (Am9511 lineage).)

- Reset default: `P0`
- Upgrade rule: `target_tier > current_tier`
- Downgrade rule: `only via RETMD`

| Tier | Value | Label | Strict |
|---:|---:|---|:---:|
| `P0` | `0` | `am9511` | true |
| `P1` | `1` | `am9512-plus` | true |
| `P2` | `2` | `am9513` | true |
| `P3` | `3` | `am9514` | true |
| `P4` | `4` | `am9515` | true |

#### Presentation Overrides

| Part | Presents As | Feature Bits | Description |
|---|---|---|---|
| `AM9512_PLUS` | `P1` | `AM9512_IEEE_PLUS` | Am9512-plus presents as P1 and advertises IEEE additions via feature bits. |
| `AM9513` | `P2` | `AM9513_ASYNC_SCALAR` | Am9513 presents as P2 and advertises async scalar capability via feature bits. |
| `AM9514` | `P3` | `AM9514_VECTOR` | Am9514 presents as P3 and advertises vector capability via feature bits. |
| `AM9515` | `P4` | `AM9515_TENSOR` | Am9515 presents as P4 and advertises tensor capability via feature bits. |

## B) Profiles

| Profile | ID | Description |
|---|---:|---|
| `PROFILE_CPU_ONLY` | `0` | CPU-only target with minimal uncore blocks. |
| `PROFILE_MCU` | `1` | Microcontroller profile with basic I/O and timers. |
| `PROFILE_SOC_RETRO` | `2` | Retro SoC profile with legacy Z80 bus adapter. |
| `PROFILE_SOC_WORKSTATION` | `3` | Workstation SoC profile with storage, DMA, and CAI accelerators. |

### Profile Requirements

| Profile | Blocks | Discovery Tables | Min Devices | Legacy Z80 Bus |
|---|---|---|---|:---:|
| `PROFILE_CPU_ONLY` | `CPU`, `CSR`, `IRQ`, `DBG` | `DISCOVERY_TABLE` |  |  |
| `PROFILE_MCU` | `CPU`, `KIO`, `TIMER`, `IRQ`, `CSR`, `DBG` | `DISCOVERY_TABLE`, `BDT` | `UART`, `TIMER` |  |
| `PROFILE_SOC_RETRO` | `CPU`, `KIO`, `TIMER`, `IRQ`, `DMA`, `STORAGE`, `CSR`, `DBG` | `DISCOVERY_TABLE`, `TOPOLOGY_TABLE`, `BDT` | `UART`, `TIMER` | true |
| `PROFILE_SOC_WORKSTATION` | `CPU`, `KIO`, `TIMER`, `IRQ`, `DMA`, `STORAGE`, `CAI`, `CSR`, `DBG` | `DISCOVERY_TABLE`, `TOPOLOGY_TABLE`, `BDT`, `LIMITS_TABLE` | `UART`, `TIMER` |  |

## C) Mode Switching Contract

### Instructions

| Instruction | Signature | Description |
|---|---|---|
| `MODEUP` | `MODEUP(target_tier, entry_vector)` | Upgrade-only transition into a higher compatibility tier. |
| `RETMD` | `RETMD()` | Return from mode (the only architectural tier downgrade mechanism). |

### MODEFLAGS

- Width: `8` bits

| Name | Bit | Reset | Description |
|---|---:|---:|---|
| `MODEFLAG_STRICT` | `0` | `1` | When 1, extension behaviors are disabled regardless of tier. |
| `MODEFLAG_INTMASK` | `1` | `0` | Architectural interrupt mask hint; when 1, mask interrupts (implementation-defined sources). |

### MODESTACK

- Minimum depth: `4`
- Recommended depth: `16`

## D) Discovery / CPUID / CAPS

- Endianness: `little`
- Leaf return words: `4` x `32`-bit
- Unknown leaf behavior: `return_zeros`

### Discovery Table (V1)

- Format: `CARBON_DISCOVERY_TABLE_V1`, version `1`, size `64` bytes

| Field | Offset | Width (bytes) | Type | Description |
|---|---:|---:|---|---|
| `signature` | `0` | `4` | `u32` | ASCII "CDSC" in little-endian (0x43534443). |
| `table_version` | `4` | `2` | `u16` | Discovery table format version (must be 1). |
| `table_size` | `6` | `2` | `u16` | Size of the discovery table in bytes (64 for v1). |
| `cpu_ladder_id` | `8` | `1` | `u8` | CPU ladder ID (TIER_LADDER_Z80). |
| `fpu_ladder_id` | `9` | `1` | `u8` | FPU ladder ID (TIER_LADDER_AM95). |
| `presented_cpu_tier` | `10` | `1` | `u8` | Presented CPU tier (P0..P15). |
| `presented_fpu_tier` | `11` | `1` | `u8` | Presented FPU tier (P0..P15). |
| `profile_id` | `12` | `1` | `u8` | Profile ID (PROFILE_*). |
| `reserved0` | `13` | `3` | `u24` | Reserved; must be 0. |
| `topology_table_ptr` | `16` | `8` | `u64` | Pointer to topology table (0 if not present). |
| `bdt_ptr` | `24` | `8` | `u64` | Pointer to BIOS Device Table (BDT) base (0 if not present). |
| `limits_table_ptr` | `32` | `8` | `u64` | Pointer to limits table (queue depths, contexts, vector widths). |
| `cpu_feature_bitmap_ptr` | `40` | `8` | `u64` | Pointer to CPU feature bitmap. |
| `fpu_feature_bitmap_ptr` | `48` | `8` | `u64` | Pointer to FPU feature bitmap. |
| `peripheral_feature_bitmap_ptr` | `56` | `8` | `u64` | Pointer to peripheral/device feature bitmap. |

### Feature Bitmap Format

- Words: `4` x `32`-bit

### Limits Table (V1)

- Format: `CARBON_LIMITS_TABLE_V1`, version `1`, size `32` bytes

| Field | Offset | Width (bytes) | Type | Description |
|---|---:|---:|---|---|
| `queue_submit_depth` | `0` | `4` | `u32` | Max CAI submit ring depth in entries. |
| `queue_complete_depth` | `4` | `4` | `u32` | Max CAI completion ring depth in entries. |
| `contexts` | `8` | `2` | `u16` | Max CAI context count. |
| `vector_lanes` | `10` | `2` | `u16` | Max vector lanes (0 if not applicable). |
| `tensor_rank` | `12` | `2` | `u16` | Max tensor rank (0 if not applicable). |
| `reserved0` | `14` | `2` | `u16` | Reserved; must be 0. |
| `max_cores` | `16` | `2` | `u16` | Max core count for topology (0 if unknown). |
| `max_threads` | `18` | `2` | `u16` | Max threads per core (SMT; 0 if unsupported). |
| `reserved1` | `20` | `12` | `u96` | Reserved; must be 0. |

### CPUID Leaf IDs

| Leaf | ID | Description |
|---|---:|---|
| `CPUID_LEAF_VENDOR` | `0x00000000` | Maximum standard leaf and vendor string. |
| `CPUID_LEAF_ID` | `0x00000001` | Vendor ID, family ID, model ID, and stepping. |
| `CPUID_LEAF_DISCOVERY` | `0x00000002` | Pointer to the canonical discovery table. |
| `CPUID_LEAF_FEATURES0` | `0x00000003` | CPU feature bitmap word0..3 (legacy mirror of discovery table). |
| `CPUID_LEAF_DEVICE_TABLE` | `0x00000004` | Legacy BDT mirror (base pointer; discovery table is canonical). |
| `CPUID_LEAF_FEATURES1` | `0x00000005` | FPU feature bitmap word0..3 (legacy mirror of discovery table). |
| `CPUID_LEAF_FEATURES2` | `0x00000006` | Peripheral/device feature bitmap word0..3 (legacy mirror of discovery table). |
| `CPUID_LEAF_CACHE0` | `0x00000010` | Cache descriptor 0 (if present; see topology table for canonical cache IDs). |
| `CPUID_LEAF_TOPOLOGY` | `0x00000011` | Legacy topology leaf (discovery table is canonical). |
| `CPUID_LEAF_ACCEL0` | `0x00000020` | Accelerator presence descriptor 0 (legacy; discovery table is canonical). |
| `CPUID_LEAF_ERRATA0` | `0x00000030` | Errata bitmap 0 (bits 0..127 across words 0..3). |

### Feature Bits

| Feature | Bit | Description |
|---|---:|---|
| `FEAT_MODE_SWITCH` | `0` | MODEUP/RETMD mode switching contract implemented. |
| `FEAT_CSR_NAMESPACE` | `1` | Carbon CSR namespace and access model implemented. |
| `FEAT_FABRIC` | `2` | Carbon internal fabric transaction contract implemented. |
| `FEAT_CPUID` | `3` | CPUID instruction transport implemented (Z480 P7). |
| `FEAT_CAPS` | `4` | CAPS transport implemented (Z85/Z90). |
| `Z85_UNDOC_Z80` | `5` | Z85 exposes undocumented Z80 opcodes/flags while presenting as P2. |
| `Z90_Z180_CLASS` | `6` | Z90 is Z180-class while presenting as P3. |
| `Z380_32BIT_EXTENDED` | `7` | Z380 provides 32-bit extended mode while presenting as P6. |
| `Z480_NATIVE_64` | `8` | Z480 provides native 64-bit mode while presenting as P7. |
| `AM9512_IEEE_PLUS` | `0` | Am9512-plus adds IEEE ports and restored Am9511 functions. |
| `AM9513_ASYNC_SCALAR` | `1` | Am9513 provides async scalar IEEE execution. |
| `AM9514_VECTOR` | `2` | Am9514 provides vector/SIMD math support. |
| `AM9515_TENSOR` | `3` | Am9515 provides matrix/tensor math support. |
| `FEAT_CAI` | `0` | Carbon Accelerator Interface (CAI) implemented. |
| `FEAT_BDT` | `1` | Board Device Table (BDT) provided for device discovery. |
| `FEAT_DEVICE_MODEL` | `2` | Device capability schema implemented for BDT entries. |
| `NON_COHERENT_DMA_BASELINE` | `3` | DMA is non-coherent by default; software must manage cache maintenance. |
| `COHERENT_DMA_OPTIONAL` | `4` | Reserved for future coherent DMA capability (optional). |

### Example CPUID Leaf Table (IDs)

| Leaf ID | Name |
|---:|---|
| `0x00000000` | `CPUID_LEAF_VENDOR` |
| `0x00000001` | `CPUID_LEAF_ID` |
| `0x00000002` | `CPUID_LEAF_DISCOVERY` |
| `0x00000003` | `CPUID_LEAF_FEATURES0` |

## E) Topology Table

- Header: `TOPOLOGY_HEADER_V1`, version `1`, size `16` bytes

| Field | Offset | Width (bytes) | Type | Description |
|---|---:|---:|---|---|
| `signature` | `0` | `4` | `u32` | ASCII "CTOP" in little-endian (0x504f5443). |
| `header_version` | `4` | `2` | `u16` | Header format version (must be 1). |
| `header_size` | `6` | `2` | `u16` | Header size in bytes (must be 16 for v1). |
| `entry_size` | `8` | `2` | `u16` | Entry size in bytes (32 for v1 entries). |
| `entry_count` | `10` | `2` | `u16` | Number of topology entries. |
| `total_size` | `12` | `4` | `u32` | Total size of the topology table (header + entries). |

- Entry: `TOPOLOGY_ENTRY_V1`, version `1`, size `32` bytes

| Field | Offset | Width (bytes) | Type | Description |
|---|---:|---:|---|---|
| `socket_id` | `0` | `2` | `u16` | Socket identifier. |
| `cluster_id` | `2` | `2` | `u16` | Cluster identifier within the socket. |
| `core_id` | `4` | `2` | `u16` | Core identifier within the cluster. |
| `thread_id` | `6` | `2` | `u16` | Thread identifier within the core (SMT index). |
| `cache_l1_id` | `8` | `2` | `u16` | L1 cache ID shared by this thread. |
| `cache_l2_id` | `10` | `2` | `u16` | L2 cache ID shared by this thread. |
| `cache_l3_id` | `12` | `2` | `u16` | L3 cache ID shared by this thread. |
| `coherence_domain_id` | `14` | `2` | `u16` | Coherence domain identifier. |
| `numa_node_id` | `16` | `2` | `u16` | NUMA node identifier. |
| `reserved0` | `18` | `14` | `u112` | Reserved; must be 0. |

## F) CSR Namespace + Register Model

- Unknown CSR behavior: `trap`

| CSR | Address | Access | Min Priv | Description |
|---|---:|---|---|---|
| `CSR_ID` | `0x00000000` | `CSR_RO` | `PRIV_U` | Read-only identification register (implementation-defined encoding). |
| `CSR_TIER` | `0x00000001` | `CSR_RW` | `PRIV_S` | Current CPU tier within the active ladder; tier changes use MODEUP/RETMD. |
| `CSR_MODEFLAGS` | `0x00000002` | `CSR_RW` | `PRIV_S` | Architectural MODEFLAGS bitfield (see mode_switch spec). |
| `CSR_TIME` | `0x00000010` | `CSR_RO` | `PRIV_U` | Cycle counter low word (or full 64-bit counter when read as 64-bit). |
| `CSR_TIME_HI` | `0x00000011` | `CSR_RO` | `PRIV_U` | Cycle counter high word (when exposed as 2x32-bit). |
| `CSR_CAUSE` | `0x00000020` | `CSR_RO` | `PRIV_S` | Trap cause metadata (encoding defined by trap/exception architecture). |
| `CSR_EPC` | `0x00000021` | `CSR_RW` | `PRIV_S` | Exception program counter (trap return address). |
| `CSR_IE` | `0x00000030` | `CSR_RW` | `PRIV_S` | Interrupt enable bits. |
| `CSR_IP` | `0x00000031` | `CSR_RO` | `PRIV_S` | Interrupt pending bits. |
| `CSR_TRACE_CTL` | `0x00000040` | `CSR_RW` | `PRIV_S` | Trace control register (trace on/off and mode bits). |
| `CSR_CPUID_LEAF` | `0x00000050` | `CSR_RW` | `PRIV_U` | CPUID leaf selector for CSR window. |
| `CSR_CPUID_SUBLEAF` | `0x00000051` | `CSR_RW` | `PRIV_U` | CPUID subleaf selector for CSR window. |
| `CSR_CPUID_DATA0_LO` | `0x00000060` | `CSR_RO` | `PRIV_U` | CPUID data word 0 (low 32 of 64). |
| `CSR_CPUID_DATA0_HI` | `0x00000061` | `CSR_RO` | `PRIV_U` | CPUID data word 0 (high 32 of 64). |
| `CSR_CPUID_DATA1_LO` | `0x00000062` | `CSR_RO` | `PRIV_U` | CPUID data word 1 (low 32 of 64). |
| `CSR_CPUID_DATA1_HI` | `0x00000063` | `CSR_RO` | `PRIV_U` | CPUID data word 1 (high 32 of 64). |
| `CSR_CPUID_DATA2_LO` | `0x00000064` | `CSR_RO` | `PRIV_U` | CPUID data word 2 (low 32 of 64). |
| `CSR_CPUID_DATA2_HI` | `0x00000065` | `CSR_RO` | `PRIV_U` | CPUID data word 2 (high 32 of 64). |
| `CSR_CPUID_DATA3_LO` | `0x00000066` | `CSR_RO` | `PRIV_U` | CPUID data word 3 (low 32 of 64). |
| `CSR_CPUID_DATA3_HI` | `0x00000067` | `CSR_RO` | `PRIV_U` | CPUID data word 3 (high 32 of 64). |
| `CSR_DBG_CTRL` | `0x00000070` | `CSR_RW` | `PRIV_S` | Debug run/halt control (CSR mirror of dbg_if). |
| `CSR_DBG_STEP` | `0x00000071` | `CSR_WO` | `PRIV_S` | Debug single-step request token (CSR mirror of dbg_if.step_req). |
| `CSR_DBG_STATUS` | `0x00000072` | `CSR_RO` | `PRIV_S` | Debug status (halted/step-ack snapshot). |
| `CSR_Z90_MMU_WIN0_BASE` | `0x00a10000` | `CSR_RW` | `PRIV_S` | Z90 MMU/window register 0 base address (register-only placeholder). |
| `CSR_Z90_MMU_WIN0_MASK` | `0x00a10004` | `CSR_RW` | `PRIV_S` | Z90 MMU/window register 0 mask/limit (register-only placeholder). |
| `CSR_Z90_MMU_WIN1_BASE` | `0x00a10008` | `CSR_RW` | `PRIV_S` | Z90 MMU/window register 1 base address (register-only placeholder). |
| `CSR_Z90_MMU_WIN1_MASK` | `0x00a1000c` | `CSR_RW` | `PRIV_S` | Z90 MMU/window register 1 mask/limit (register-only placeholder). |
| `CSR_Z90_CACHE_CTL` | `0x00a10010` | `CSR_RW` | `PRIV_S` | Z90 cache control hooks (register-only placeholder; no cache logic implied). |
| `CSR_Z90_ATOMIC_CTL` | `0x00a10014` | `CSR_RW` | `PRIV_S` | Z90 atomic enable/control (register-only placeholder). |
| `CSR_Z90_ATOMIC_STATUS` | `0x00a10018` | `CSR_RO` | `PRIV_S` | Z90 atomic status (register-only placeholder). |
| `CSR_8097_ID` | `0x00a30000` | `CSR_RO` | `PRIV_U` | 8097 identification register (implementation-defined encoding). |
| `CSR_8097_TIER` | `0x00a30004` | `CSR_RW` | `PRIV_S` | 8097 active tier (x86-derived ladder); v1 only supports P0 and P7. |
| `CSR_8097_MODEFLAGS` | `0x00a30008` | `CSR_RW` | `PRIV_S` | 8097 modeflags (STRICT/INTMASK); STRICT gates turbo extensions. |
| `CSR_8097_STATUS` | `0x00a3000c` | `CSR_RO` | `PRIV_U` | 8097 status (busy, stack state, last fault). |
| `CSR_8097_CTRL_WORD` | `0x00a30010` | `CSR_RW` | `PRIV_S` | 8097 control word (v1: rounding control subset). |
| `CSR_8097_STATUS_WORD` | `0x00a30014` | `CSR_RO` | `PRIV_U` | 8097 status word (v1: condition codes + basic exception summary). |
| `CSR_8097_MEM_ADDR_LO` | `0x00a30018` | `CSR_RW` | `PRIV_U` | 8097 memory address low word for FLD/FSTP commands. |
| `CSR_8097_MEM_ADDR_HI` | `0x00a3001c` | `CSR_RW` | `PRIV_U` | 8097 memory address high word for FLD/FSTP commands. |
| `CSR_8097_PUSH_LO` | `0x00a30020` | `CSR_WO` | `PRIV_U` | 8097 push data low word (64-bit); write LO then HI to push. |
| `CSR_8097_PUSH_HI` | `0x00a30024` | `CSR_WO` | `PRIV_U` | 8097 push data high word; triggers stack push. |
| `CSR_8097_POP_LO` | `0x00a30028` | `CSR_RO` | `PRIV_U` | 8097 pop data low word (peek ST0 low 32). |
| `CSR_8097_POP_HI` | `0x00a3002c` | `CSR_RO` | `PRIV_U` | 8097 pop data high word (returns ST0 high 32 and pops). |
| `CSR_8097_CMD` | `0x00a30030` | `CSR_WO` | `PRIV_U` | 8097 command register; writing triggers an x87-like operation. |
| `CSR_8097_RF_INDEX` | `0x00a30034` | `CSR_RW` | `PRIV_S` | 8097 turbo RF index (F0..F15) for P7 regfile mode. |
| `CSR_8097_RF_DATA_LO` | `0x00a30038` | `CSR_RW` | `PRIV_S` | 8097 turbo RF data low word. |
| `CSR_8097_RF_DATA_HI` | `0x00a3003c` | `CSR_RW` | `PRIV_S` | 8097 turbo RF data high word. |
| `CSR_8097_RF_OP` | `0x00a30040` | `CSR_WO` | `PRIV_S` | 8097 turbo RF operation (P7-only, packed indices/opcode). |
| `CSR_AM9513_ID` | `0x00700000` | `CSR_RO` | `PRIV_U` | Am9513 identification register (implementation-defined encoding). |
| `CSR_AM9513_CTRL` | `0x00700004` | `CSR_RW` | `PRIV_S` | Am9513 global control (v1.0: enable). |
| `CSR_AM9513_STATUS` | `0x00700008` | `CSR_RO` | `PRIV_U` | Am9513 global status (busy, pending work, last fault). |
| `CSR_AM9513_MODE` | `0x0070000c` | `CSR_RW` | `PRIV_S` | Default personality/mode select (P0/P1/P2 with P3/P4 reserved) for non-CAI paths. |
| `CSR_AM9513_CTX_SEL` | `0x00700010` | `CSR_RW` | `PRIV_U` | Context selector for CSR register-file/legacy windows. |
| `CSR_AM9513_CTX_RM` | `0x00700014` | `CSR_RW` | `PRIV_U` | Per-context IEEE rounding mode (uses formats spec rounding IDs). |
| `CSR_AM9513_CTX_FLAGS` | `0x00700018` | `CSR_RO` | `PRIV_U` | Per-context IEEE exception flags (sticky). |
| `CSR_AM9513_CTX_FLAGS_CLR` | `0x0070001c` | `CSR_WO` | `PRIV_U` | Write-1-to-clear bits for per-context IEEE exception flags. |
| `CSR_AM9513_RF_INDEX` | `0x00700020` | `CSR_RW` | `PRIV_U` | Register-file index selector (F0..F15) for RF_DATA reads/writes. |
| `CSR_AM9513_RF_DATA_LO` | `0x00700024` | `CSR_RW` | `PRIV_U` | Register-file data low word for selected context/register. |
| `CSR_AM9513_RF_DATA_HI` | `0x00700028` | `CSR_RW` | `PRIV_U` | Register-file data high word for selected context/register. |
| `CSR_AM9513_CAI_COMP_BASE_LO` | `0x00700030` | `CSR_RW` | `PRIV_S` | CAI completion ring base address (low word). |
| `CSR_AM9513_CAI_COMP_BASE_HI` | `0x00700034` | `CSR_RW` | `PRIV_S` | CAI completion ring base address (high word). |
| `CSR_AM9513_CAI_COMP_RING_MASK` | `0x00700038` | `CSR_RW` | `PRIV_S` | CAI completion ring mask (entries-1, power-of-two ring). |
| `CSR_AM9513_CAI_IRQ_ENABLE` | `0x0070003c` | `CSR_RW` | `PRIV_S` | CAI completion interrupt enable (maps to cai_if.comp_irq). |
| `CSR_AM9513_LEGACY_CTRL` | `0x00700040` | `CSR_RW` | `PRIV_U` | Legacy 9511/9512 CSR window control (mode/format selection). |
| `CSR_AM9513_LEGACY_STATUS` | `0x00700044` | `CSR_RO` | `PRIV_U` | Legacy 9511/9512 status (busy, stack depth, error). |
| `CSR_AM9513_LEGACY_PUSH_LO` | `0x00700048` | `CSR_WO` | `PRIV_U` | Legacy push operand low word (commit via PUSH_HI write). |
| `CSR_AM9513_LEGACY_PUSH_HI` | `0x0070004c` | `CSR_WO` | `PRIV_U` | Legacy push operand high word (writing commits a push). |
| `CSR_AM9513_LEGACY_POP_LO` | `0x00700050` | `CSR_RO` | `PRIV_U` | Legacy pop result low word (read does not pop; POP_HI commits pop). |
| `CSR_AM9513_LEGACY_POP_HI` | `0x00700054` | `CSR_RO` | `PRIV_U` | Legacy pop result high word (read triggers pop side-effect). |
| `CSR_AM9513_LEGACY_OP` | `0x00700058` | `CSR_WO` | `PRIV_U` | Legacy operation issue (opcode-defined stack operands/results). |
| `CSR_CARBONIO_ID` | `0x00300000` | `CSR_RO` | `PRIV_U` | CarbonIO identification register (implementation-defined encoding). |
| `CSR_CARBONIO_STATUS` | `0x00300001` | `CSR_RO` | `PRIV_U` | CarbonIO status summary (busy/error). |
| `CSR_CARBONIO_CTRL` | `0x00300002` | `CSR_RW` | `PRIV_S` | CarbonIO control (enable/reset). |
| `CSR_CARBONIO_MODE` | `0x00300003` | `CSR_RW` | `PRIV_S` | CarbonIO personality/mode selection. |
| `CSR_CARBONIO_FEATURE0` | `0x00300004` | `CSR_RO` | `PRIV_U` | CarbonIO feature word 0 (descriptor mirror). |
| `CSR_CARBONIO_FEATURE1` | `0x00300005` | `CSR_RO` | `PRIV_U` | CarbonIO feature word 1 (descriptor mirror). |
| `CSR_CARBONIO_QUEUE_SUBMIT_BASE_LO` | `0x00300010` | `CSR_RW` | `PRIV_S` | Turbo submission ring base (low 32). |
| `CSR_CARBONIO_QUEUE_SUBMIT_BASE_HI` | `0x00300011` | `CSR_RW` | `PRIV_S` | Turbo submission ring base (high 32). |
| `CSR_CARBONIO_QUEUE_SUBMIT_MASK` | `0x00300012` | `CSR_RW` | `PRIV_S` | Turbo submission ring mask (entries-1). |
| `CSR_CARBONIO_QUEUE_DOORBELL` | `0x00300013` | `CSR_WO` | `PRIV_S` | Turbo submission doorbell. |
| `CSR_CARBONIO_QUEUE_COMP_BASE_LO` | `0x00300014` | `CSR_RW` | `PRIV_S` | Turbo completion ring base (low 32). |
| `CSR_CARBONIO_QUEUE_COMP_BASE_HI` | `0x00300015` | `CSR_RW` | `PRIV_S` | Turbo completion ring base (high 32). |
| `CSR_CARBONIO_QUEUE_COMP_MASK` | `0x00300016` | `CSR_RW` | `PRIV_S` | Turbo completion ring mask (entries-1). |
| `CSR_CARBONIO_QUEUE_COMP_DOORBELL` | `0x00300017` | `CSR_RO` | `PRIV_U` | Completion doorbell (device -> host). |
| `CSR_CARBONIO_QUEUE_STATUS` | `0x00300018` | `CSR_RO` | `PRIV_U` | Turbo queue status. |
| `CSR_CARBONIO_PERF0` | `0x00300020` | `CSR_RO` | `PRIV_U` | Performance counter 0 (device-defined). |
| `CSR_CARBONIO_PERF1` | `0x00300021` | `CSR_RO` | `PRIV_U` | Performance counter 1 (device-defined). |
| `CSR_CARBONIO_UART_CFG` | `0x00300030` | `CSR_RW` | `PRIV_U` | UART configuration (enable, format, timestamp). |
| `CSR_CARBONIO_UART_STATUS` | `0x00300031` | `CSR_RO` | `PRIV_U` | UART status (FIFO state, errors). |
| `CSR_CARBONIO_UART_RX_COUNT` | `0x00300032` | `CSR_RO` | `PRIV_U` | UART RX FIFO count. |
| `CSR_CARBONIO_UART_TX_COUNT` | `0x00300033` | `CSR_RO` | `PRIV_U` | UART TX FIFO count. |
| `CSR_CARBONIO_UART_TX_WDATA` | `0x00300034` | `CSR_WO` | `PRIV_U` | UART TX data write (push to FIFO). |
| `CSR_CARBONIO_UART_RX_RDATA` | `0x00300035` | `CSR_RO` | `PRIV_U` | UART RX data read (pop from FIFO). |
| `CSR_CARBONIO_UART_WATERMARKS` | `0x00300036` | `CSR_RW` | `PRIV_U` | UART RX/TX FIFO watermark levels. |
| `CSR_CARBONIO_UART_TS_LO` | `0x00300037` | `CSR_RO` | `PRIV_U` | UART timestamp low word (optional). |
| `CSR_CARBONIO_UART_TS_HI` | `0x00300038` | `CSR_RO` | `PRIV_U` | UART timestamp high word (optional). |
| `CSR_CARBONIO_PIO_IN` | `0x00300040` | `CSR_RO` | `PRIV_U` | PIO input value snapshot. |
| `CSR_CARBONIO_PIO_OUT` | `0x00300041` | `CSR_RW` | `PRIV_U` | PIO output latch. |
| `CSR_CARBONIO_PIO_DIR` | `0x00300042` | `CSR_RW` | `PRIV_U` | PIO direction (1=output). |
| `CSR_CARBONIO_PIO_EDGE_RDATA` | `0x00300043` | `CSR_RO` | `PRIV_U` | PIO edge capture FIFO read. |
| `CSR_CARBONIO_PIO_EDGE_COUNT` | `0x00300044` | `CSR_RO` | `PRIV_U` | PIO edge capture FIFO count. |
| `CSR_CARBONIO_PIO_FILTER_CFG` | `0x00300045` | `CSR_RW` | `PRIV_U` | PIO glitch filter configuration (basic v1). |
| `CSR_CARBONIO_PIO_MATCH_CFG` | `0x00300046` | `CSR_RW` | `PRIV_U` | PIO pattern match configuration (basic v1). |
| `CSR_CARBONIO_TICK_LO` | `0x00300050` | `CSR_RO` | `PRIV_U` | Monotonic tick counter low word. |
| `CSR_CARBONIO_TICK_HI` | `0x00300051` | `CSR_RO` | `PRIV_U` | Monotonic tick counter high word. |
| `CSR_CARBONIO_TIMER0_LOAD` | `0x00300052` | `CSR_RW` | `PRIV_U` | Timer0 reload value. |
| `CSR_CARBONIO_TIMER0_VALUE` | `0x00300053` | `CSR_RO` | `PRIV_U` | Timer0 current value. |
| `CSR_CARBONIO_TIMER0_CTRL` | `0x00300054` | `CSR_RW` | `PRIV_U` | Timer0 control (enable/periodic). |
| `CSR_CARBONIO_TIMER0_STATUS` | `0x00300055` | `CSR_RO` | `PRIV_U` | Timer0 status (expired). |
| `CSR_CARBONIO_TIMER1_LOAD` | `0x00300056` | `CSR_RW` | `PRIV_U` | Timer1 reload value. |
| `CSR_CARBONIO_TIMER1_VALUE` | `0x00300057` | `CSR_RO` | `PRIV_U` | Timer1 current value. |
| `CSR_CARBONIO_TIMER1_CTRL` | `0x00300058` | `CSR_RW` | `PRIV_U` | Timer1 control (enable/periodic). |
| `CSR_CARBONIO_TIMER1_STATUS` | `0x00300059` | `CSR_RO` | `PRIV_U` | Timer1 status (expired). |
| `CSR_CARBONIO_IRQ_ENABLE` | `0x00300060` | `CSR_RW` | `PRIV_U` | IRQ enable bits for CarbonIO sources. |
| `CSR_CARBONIO_IRQ_PENDING` | `0x00300061` | `CSR_RO` | `PRIV_U` | IRQ pending bits for CarbonIO sources. |
| `CSR_CARBONIO_IRQ_MASK` | `0x00300062` | `CSR_RW` | `PRIV_U` | IRQ mask/clear bits for CarbonIO sources. |
| `CSR_CARBONPIC_ID` | `0x00310000` | `CSR_RO` | `PRIV_U` | CarbonPIC identification register. |
| `CSR_CARBONPIC_STATUS` | `0x00310001` | `CSR_RO` | `PRIV_U` | CarbonPIC status summary. |
| `CSR_CARBONPIC_CTRL` | `0x00310002` | `CSR_RW` | `PRIV_S` | CarbonPIC control (enable/reset). |
| `CSR_CARBONPIC_MODE` | `0x00310003` | `CSR_RW` | `PRIV_S` | CarbonPIC mode configuration. |
| `CSR_CARBONPIC_FEATURE0` | `0x00310004` | `CSR_RO` | `PRIV_U` | CarbonPIC feature word 0. |
| `CSR_CARBONPIC_FEATURE1` | `0x00310005` | `CSR_RO` | `PRIV_U` | CarbonPIC feature word 1. |
| `CSR_CARBONPIC_SRC_INDEX` | `0x00310020` | `CSR_RW` | `PRIV_U` | Source index selector for per-source registers. |
| `CSR_CARBONPIC_SRC_PRIORITY` | `0x00310021` | `CSR_RW` | `PRIV_U` | Priority value for selected source. |
| `CSR_CARBONPIC_SRC_TARGETS` | `0x00310022` | `CSR_RW` | `PRIV_U` | Target routing mask for selected source. |
| `CSR_CARBONPIC_SRC_ENABLE` | `0x00310023` | `CSR_RW` | `PRIV_U` | Enable bit for selected source. |
| `CSR_CARBONPIC_SRC_PENDING` | `0x00310024` | `CSR_RO` | `PRIV_U` | Pending status for selected source. |
| `CSR_CARBONPIC_GLOBAL_PENDING` | `0x00310025` | `CSR_RO` | `PRIV_U` | Global pending bitmap. |
| `CSR_CARBONDMA_ID` | `0x00600000` | `CSR_RO` | `PRIV_U` | CarbonDMA identification register. |
| `CSR_CARBONDMA_STATUS` | `0x00600001` | `CSR_RO` | `PRIV_U` | CarbonDMA status summary. |
| `CSR_CARBONDMA_CTRL` | `0x00600002` | `CSR_RW` | `PRIV_S` | CarbonDMA control (enable/reset). |
| `CSR_CARBONDMA_MODE` | `0x00600003` | `CSR_RW` | `PRIV_S` | CarbonDMA mode configuration. |
| `CSR_CARBONDMA_FEATURE0` | `0x00600004` | `CSR_RO` | `PRIV_U` | CarbonDMA feature word 0. |
| `CSR_CARBONDMA_FEATURE1` | `0x00600005` | `CSR_RO` | `PRIV_U` | CarbonDMA feature word 1. |
| `CSR_CARBONDMA_QUEUE_SUBMIT_BASE_LO` | `0x00600010` | `CSR_RW` | `PRIV_S` | Turbo submission ring base (low 32). |
| `CSR_CARBONDMA_QUEUE_SUBMIT_BASE_HI` | `0x00600011` | `CSR_RW` | `PRIV_S` | Turbo submission ring base (high 32). |
| `CSR_CARBONDMA_QUEUE_SUBMIT_MASK` | `0x00600012` | `CSR_RW` | `PRIV_S` | Turbo submission ring mask (entries-1). |
| `CSR_CARBONDMA_QUEUE_DOORBELL` | `0x00600013` | `CSR_WO` | `PRIV_S` | Turbo submission doorbell. |
| `CSR_CARBONDMA_QUEUE_COMP_BASE_LO` | `0x00600014` | `CSR_RW` | `PRIV_S` | Turbo completion ring base (low 32). |
| `CSR_CARBONDMA_QUEUE_COMP_BASE_HI` | `0x00600015` | `CSR_RW` | `PRIV_S` | Turbo completion ring base (high 32). |
| `CSR_CARBONDMA_QUEUE_COMP_MASK` | `0x00600016` | `CSR_RW` | `PRIV_S` | Turbo completion ring mask (entries-1). |
| `CSR_CARBONDMA_QUEUE_COMP_DOORBELL` | `0x00600017` | `CSR_RO` | `PRIV_U` | Completion doorbell (device -> host). |
| `CSR_CARBONDMA_QUEUE_STATUS` | `0x00600018` | `CSR_RO` | `PRIV_U` | Turbo queue status. |
| `CSR_CARBONDMA_CH_SEL` | `0x00600020` | `CSR_RW` | `PRIV_S` | Channel index selector for compatibility mode. |
| `CSR_CARBONDMA_CH_SRC_LO` | `0x00600021` | `CSR_RW` | `PRIV_S` | Channel source base low word. |
| `CSR_CARBONDMA_CH_SRC_HI` | `0x00600022` | `CSR_RW` | `PRIV_S` | Channel source base high word. |
| `CSR_CARBONDMA_CH_DST_LO` | `0x00600023` | `CSR_RW` | `PRIV_S` | Channel destination base low word. |
| `CSR_CARBONDMA_CH_DST_HI` | `0x00600024` | `CSR_RW` | `PRIV_S` | Channel destination base high word. |
| `CSR_CARBONDMA_CH_LEN` | `0x00600025` | `CSR_RW` | `PRIV_S` | Channel transfer length in bytes. |
| `CSR_CARBONDMA_CH_CTRL` | `0x00600026` | `CSR_RW` | `PRIV_S` | Channel control (start/opcode/flags). |
| `CSR_CARBONDMA_CH_STATUS` | `0x00600027` | `CSR_RO` | `PRIV_S` | Channel status (busy/done/fault). |
| `CSR_CARBONDMA_CH_ATTR` | `0x00600028` | `CSR_RW` | `PRIV_S` | Channel fabric attribute overrides. |
| `CSR_CARBONDMA_CH_FILL` | `0x00600029` | `CSR_RW` | `PRIV_S` | Channel fill pattern (for fill opcode). |

## G) Memory Attributes

- Width: `8` bits

| Name | Bit | Description |
|---|---:|---|
| `MEM_ATTR_CACHEABLE` | `0` | 1=cacheable, 0=uncacheable. |
| `MEM_ATTR_ORDERED` | `1` | 1=ordered, 0=normal ordering. |
| `MEM_ATTR_IO_SPACE` | `2` | 1=I/O space semantics, 0=memory space semantics. |
| `MEM_ATTR_ACQUIRE` | `3` | Acquire semantics for synchronization. |
| `MEM_ATTR_RELEASE` | `4` | Release semantics for synchronization. |

### DMA Coherence Baseline

- Baseline: `non_coherent`
- DMA engines must honor MEM_ATTR_ORDERED for ordered transactions.
- Non-coherent DMA requires explicit cache clean/invalidate around buffer usage.

### P7 Cache Maintenance Hooks

- `cache_clean_range`: Write back dirty cache lines for the specified range.
- `cache_invalidate_range`: Invalidate cache lines for the specified range.
- `cache_clean_invalidate_range`: Clean and invalidate cache lines for the specified range.

## H) Fabric Transaction Contract

### Transaction Types

| Name | Value | Description |
|---|---:|---|
| `FABRIC_XACT_READ` | `0` | Read from memory or IO space. |
| `FABRIC_XACT_WRITE` | `1` | Write to memory or IO space. |
| `FABRIC_XACT_ATOMIC` | `2` | Atomic operation (minimum set defined by implementation profile). |
| `FABRIC_XACT_MESSAGE` | `3` | Message packet (mailboxes, interrupts, doorbells). |
| `FABRIC_XACT_DMA_DESC` | `4` | DMA descriptor transaction (may also be encoded as a message). |

### Attributes

| Field | LSB | Width | Description |
|---|---:|---:|---|
| `MEM_ATTR_CACHEABLE` | `0` | `1` | 1=cacheable, 0=uncacheable. |
| `MEM_ATTR_ORDERED` | `1` | `1` | 1=ordered, 0=normal ordering. |
| `MEM_ATTR_IO_SPACE` | `2` | `1` | 1=IO space, 0=memory space. |
| `MEM_ATTR_ACQUIRE` | `3` | `1` | Acquire semantics (for synchronization). |
| `MEM_ATTR_RELEASE` | `4` | `1` | Release semantics (for synchronization). |
| `FABRIC_ATTR_BURST_HINT` | `5` | `3` | Burst length hint (0=unspecified; other values are implementation-defined hints). |
| `FABRIC_ATTR_QOS` | `8` | `4` | QoS/priority (reserved if not implemented; must be ignored if unsupported). |

### Response Codes

| Name | Value | Description |
|---|---:|---|
| `FABRIC_RESP_OK` | `0` | Transaction completed successfully. |
| `FABRIC_RESP_DECODE_ERR` | `1` | Address decode error (no target). |
| `FABRIC_RESP_ACCESS_FAULT` | `2` | Access permission fault. |
| `FABRIC_RESP_TIMEOUT` | `3` | Target timeout or no response. |
| `FABRIC_RESP_ECC_ERR` | `4` | ECC or integrity error (reserved if not implemented). |

## I) Carbon Accelerator Interface (CAI)

### Opcode Groups

| Name | Value | Description |
|---|---:|---|
| `AM95_SCALAR` | `0` | Am95xx scalar math operations (Am9512+/Am9513 class). |
| `AM95_VECTOR` | `1` | Am95xx vector/SIMD math operations (Am9514 class). |
| `AM95_TENSOR` | `2` | Am95xx matrix/tensor operations (Am9515 class). |
| `DMA_COPY` | `3` | Future DMA copy operations. |
| `DMA_FILL` | `4` | Future DMA fill operations. |
| `UART_STREAM` | `5` | Future UART stream operations. |

### Submission Descriptor (V1)

- Format: `CAI_SUBMIT_DESC_V1`, version `1`, size `64` bytes

| Field | Offset | Width (bytes) | Type | Description |
|---|---:|---:|---|---|
| `desc_version` | `0` | `2` | `u16` | Descriptor format version (must be 1 for v1.0). |
| `desc_size_dw` | `2` | `2` | `u16` | Descriptor size in 32-bit words (must be 16 for this format). |
| `opcode` | `4` | `4` | `u32` | Operation code within the opcode_group namespace. |
| `flags` | `8` | `4` | `u32` | Operation flags (reserved bits must be 0). |
| `context_id` | `12` | `2` | `u16` | Context identifier. |
| `operand_count` | `14` | `2` | `u16` | Number of operand descriptors in the operand list. |
| `tag` | `16` | `4` | `u32` | Opaque tag returned in the completion record. |
| `opcode_group` | `20` | `1` | `u8` | Opcode group selector (see opcode_model.opcode_groups). |
| `format_primary` | `21` | `1` | `u8` | Primary numeric format ID (see formats spec). |
| `format_aux` | `22` | `1` | `u8` | Secondary numeric format ID (vector element or auxiliary format). |
| `format_flags` | `23` | `1` | `u8` | Format flags/reserved (must be 0). |
| `operands_ptr` | `24` | `8` | `u64` | Pointer to an array of operand descriptors. |
| `result_ptr` | `32` | `8` | `u64` | Pointer to the result buffer. |
| `result_len` | `40` | `4` | `u32` | Result length in bytes (or elements, opcode-defined). |
| `result_stride` | `44` | `4` | `u32` | Stride in bytes between result elements (0=contiguous). |
| `tensor_desc_ptr` | `48` | `8` | `u64` | Optional pointer to tensor descriptor for P4 operations (0 if unused). |
| `tensor_desc_len` | `56` | `2` | `u16` | Tensor descriptor length in bytes (0 if unused). |
| `tensor_rank` | `58` | `1` | `u8` | Tensor rank (0 if unused). |
| `tensor_desc_flags` | `59` | `1` | `u8` | Tensor descriptor flags (reserved). |
| `reserved2` | `60` | `4` | `u32` | Reserved; must be 0. |

### Operand Descriptor (V1)

- Format: `CAI_OPERAND_DESC_V1`, version `1`, size `32` bytes

| Field | Offset | Width (bytes) | Type | Description |
|---|---:|---:|---|---|
| `ptr` | `0` | `8` | `u64` | Pointer to operand buffer. |
| `len` | `8` | `4` | `u32` | Operand length in bytes (or elements, opcode-defined). |
| `stride` | `12` | `4` | `u32` | Stride in bytes between operand elements (0=contiguous). |
| `flags` | `16` | `4` | `u32` | Operand flags (reserved if not implemented). |
| `reserved0` | `20` | `4` | `u32` | Reserved; must be 0. |
| `reserved1` | `24` | `8` | `u64` | Reserved; must be 0. |

### Tensor Descriptor (V1)

- Format: `CAI_TENSOR_DESC_V1`, version `1`, size `64` bytes

| Field | Offset | Width (bytes) | Type | Description |
|---|---:|---:|---|---|
| `desc_version` | `0` | `2` | `u16` | Descriptor format version (must be 1 for v1.0). |
| `desc_size_dw` | `2` | `2` | `u16` | Descriptor size in 32-bit words (must be 16 for this format). |
| `rank` | `4` | `1` | `u8` | Tensor rank (number of dimensions). |
| `elem_format` | `5` | `1` | `u8` | Element numeric format ID (see formats spec). |
| `reserved0` | `6` | `2` | `u16` | Reserved; must be 0. |
| `flags` | `8` | `4` | `u32` | Tensor descriptor flags (reserved). |
| `shape0` | `12` | `4` | `u32` | Dimension 0 length. |
| `shape1` | `16` | `4` | `u32` | Dimension 1 length. |
| `shape2` | `20` | `4` | `u32` | Dimension 2 length. |
| `shape3` | `24` | `4` | `u32` | Dimension 3 length. |
| `stride0` | `28` | `4` | `u32` | Dimension 0 stride in elements. |
| `stride1` | `32` | `4` | `u32` | Dimension 1 stride in elements. |
| `stride2` | `36` | `4` | `u32` | Dimension 2 stride in elements. |
| `stride3` | `40` | `4` | `u32` | Dimension 3 stride in elements. |
| `reserved1` | `44` | `4` | `u32` | Reserved; must be 0. |
| `reserved2` | `48` | `8` | `u64` | Reserved; must be 0. |
| `reserved3` | `56` | `8` | `u64` | Reserved; must be 0. |

### Completion Record (V1)

- Format: `CAI_COMP_REC_V1`, version `1`, size `16` bytes

| Field | Offset | Width (bytes) | Type | Description |
|---|---:|---:|---|---|
| `tag` | `0` | `4` | `u32` | Tag from the submission descriptor. |
| `status` | `4` | `2` | `u16` | Completion status code. |
| `ext_status` | `6` | `2` | `u16` | Optional extended status (e.g. IEEE flags for Am9513). |
| `bytes_written` | `8` | `4` | `u32` | Optional byte count written to result (0 if unused). |
| `reserved0` | `12` | `4` | `u32` | Reserved; must be 0. |

### Completion Status Codes

| Name | Value | Description |
|---|---:|---|
| `CAI_STATUS_OK` | `0` | Success. |
| `CAI_STATUS_INVALID_OP` | `1` | Unsupported/invalid opcode. |
| `CAI_STATUS_FAULT` | `2` | Access fault or invalid pointer/length. |
| `CAI_STATUS_TIMEOUT` | `3` | Operation timeout. |
| `CAI_STATUS_UNSUPPORTED` | `4` | Feature unsupported for this device/context. |

### Example Submission Descriptor

```text
desc_version: 1
desc_size_dw: 16
opcode: 0
flags: 0
context_id: 0
operand_count: 2
tag: 305419896
opcode_group: 0
format_primary: 0
format_aux: 0
format_flags: 0
operands_ptr: 268435456
result_ptr: 536870912
result_len: 256
result_stride: 0
tensor_desc_ptr: 0
tensor_desc_len: 0
tensor_rank: 0
tensor_desc_flags: 0
```

## J) Device Model and BDT Schema

### Dual Personality Device Model

- Universal model for all Carbon devices; each device exposes a compatibility personality and a turbo personality.

### Compatibility Personality

- Ordered I/O semantics; reads and writes observe program order.
- WAIT/ready backpressure is honored; no hidden reordering.
- Registers are deterministic; no turbo-only side effects.

### Turbo Personality

- Uses fast data-plane paths (queues, DMA, or large FIFOs).
- May complete at different speeds than compatibility mode, but results must match.
- Turbo features are gated by MODEFLAGS and tier policy.

### Polling-Complete Semantics

- Every operation must have a completion indicator that can be polled without interrupts.
- Completion indicators must be deterministic and monotonic for a given operation.
- Interrupts, if present, are optional accelerators for the same completion state.

### Device Class IDs

| Class | Value | Description |
|---|---:|---|
| `DEVCLASS_CPU` | `0x0001` | CPU cores. |
| `DEVCLASS_ACCEL` | `0x0002` | FPU/accelerator cores (Am95xx-class). |
| `DEVCLASS_UART` | `0x0010` | UART console devices. |
| `DEVCLASS_PIO` | `0x0012` | GPIO/PIO controllers. |
| `DEVCLASS_TIMER` | `0x0013` | Timers/CTC blocks and monotonic ticks. |
| `DEVCLASS_PIC` | `0x0014` | Interrupt controllers / routers. |
| `DEVCLASS_DMA` | `0x0020` | DMA engines (mem-to-mem, scatter/gather). |
| `DEVCLASS_STORAGE` | `0x0030` | Storage devices (block or character). |

### BDT Header (V1)

- Format: `BDT_HEADER_V1`, version `1`, size `16` bytes

| Field | Offset | Width (bytes) | Type | Description |
|---|---:|---:|---|---|
| `signature` | `0` | `4` | `u32` | ASCII "CBDT" in little-endian (0x54444243). |
| `header_version` | `4` | `2` | `u16` | Header format version (must be 1). |
| `header_size` | `6` | `2` | `u16` | Header size in bytes (must be 16 for v1). |
| `entry_size` | `8` | `2` | `u16` | BDT entry size in bytes (64 for v1 entries). |
| `entry_count` | `10` | `2` | `u16` | Number of device entries in the BDT. |
| `total_size` | `12` | `4` | `u32` | Total size of the BDT region (header + entries). |

### BDT Entry (V1)

- Format: `BDT_ENTRY_V1`, version `1`, size `64` bytes

| Field | Offset | Width (bytes) | Type | Description |
|---|---:|---:|---|---|
| `desc_version` | `0` | `2` | `u16` | Descriptor format version (must be 1). |
| `desc_size_bytes` | `2` | `2` | `u16` | Descriptor size in bytes (64 for v1). |
| `class_id` | `4` | `2` | `u16` | Device class identifier (see device_classes). |
| `subclass_id` | `6` | `2` | `u16` | Device subclass identifier (0 if unused). |
| `instance_id` | `8` | `2` | `u16` | Instance index for multiple identical devices. |
| `device_version` | `10` | `2` | `u16` | Device version ID (implementation-defined). |
| `caps0` | `12` | `4` | `u32` | Capability flags word 0. |
| `caps1` | `16` | `4` | `u32` | Capability flags word 1. |
| `irq_route_offset` | `20` | `2` | `u16` | Offset (bytes) from BDT base to IRQ routing table (0 if none). |
| `irq_route_count` | `22` | `2` | `u16` | Number of IRQ routing entries (0 if none). |
| `mmio_base` | `24` | `8` | `u64` | MMIO base address (0 if none). |
| `mmio_size` | `32` | `4` | `u32` | MMIO window size in bytes (0 if none). |
| `io_port_base` | `36` | `4` | `u32` | I/O port base (0 if none). |
| `io_port_size` | `40` | `2` | `u16` | I/O port window size in bytes (0 if none). |
| `block_sector_size` | `42` | `2` | `u16` | Logical sector size for block devices (must support 512). |
| `cai_queue_count` | `44` | `2` | `u16` | CAI queue count (0 if device is not CAI-capable). |
| `cai_doorbell_offset` | `46` | `2` | `u16` | CSR offset to CAI doorbell register (0 if not applicable). |
| `reserved0` | `48` | `16` | `u128` | Reserved; must be 0. |

### BDT IRQ Routing Entry (V1)

- Entry size: `8` bytes

| Field | Offset | Width (bytes) | Type | Description |
|---|---:|---:|---|---|
| `domain_id` | `0` | `2` | `u16` | Interrupt domain identifier (PIC instance). |
| `irq_line` | `2` | `2` | `u16` | IRQ line or vector within the domain. |
| `flags` | `4` | `2` | `u16` | IRQ flags (level/edge polarity; reserved if unused). |
| `reserved0` | `6` | `2` | `u16` | Reserved; must be 0. |

### Device Capability Descriptor (V1)

- Format: `DEVICE_CAP_DESC_V1`, version `1`, size `64` bytes

| Field | Offset | Width (bytes) | Type | Description |
|---|---:|---:|---|---|
| `desc_version` | `0` | `2` | `u16` | Descriptor format version (must be 1). |
| `desc_size_bytes` | `2` | `2` | `u16` | Descriptor size in bytes (must be 64 for v1). |
| `class_id` | `4` | `2` | `u16` | Primary device class ID (see device_classes). |
| `subclass_id` | `6` | `2` | `u16` | Subclass ID within the device class (0 if unused). |
| `vendor_id` | `8` | `2` | `u16` | Vendor ID (0x0000 for Project Carbon). |
| `device_id` | `10` | `2` | `u16` | Device ID within the vendor namespace. |
| `instance_id` | `12` | `2` | `u16` | Instance index for multiple identical devices. |
| `revision_id` | `14` | `2` | `u16` | Device revision ID (implementation-defined). |
| `compat_flags` | `16` | `4` | `u32` | Compatibility personality feature flags (compat_feature_bits). |
| `turbo_flags` | `20` | `4` | `u32` | Turbo personality feature flags (turbo_feature_bits). |
| `feature_word0` | `24` | `4` | `u32` | Standard numeric feature fields (feature_fields word 0). |
| `feature_word1` | `28` | `4` | `u32` | Standard numeric feature fields (feature_fields word 1). |
| `csr_base` | `32` | `8` | `u64` | CSR base address (0 if none). |
| `compat_io_base` | `40` | `8` | `u64` | Compatibility I/O base (port or MMIO base; 0 if none). |
| `mmio_base` | `48` | `8` | `u64` | High-level MMIO base for device windows (0 if none). |
| `mmio_size` | `56` | `4` | `u32` | MMIO window size in bytes (0 if none). |
| `queue_count` | `60` | `2` | `u16` | Number of turbo queues exposed by the device. |
| `irq_count` | `62` | `2` | `u16` | Number of IRQ sources exposed by the device. |

### Device Compatibility Feature Bits

| Feature | Bit | Description |
|---|---:|---|
| `DEVFEAT_COMPAT_POLLING` | `0` | Polling-complete semantics implemented. |
| `DEVFEAT_COMPAT_IRQ` | `1` | Interrupts implemented (optional for completion). |
| `DEVFEAT_COMPAT_PORT_IO` | `2` | Compatibility register map can be exposed on I/O space. |
| `DEVFEAT_COMPAT_MMIO` | `3` | Compatibility register map can be exposed on MMIO space. |
| `DEVFEAT_COMPAT_WAIT` | `4` | WAIT/backpressure on compatibility accesses is honored. |

### Device Turbo Feature Bits

| Feature | Bit | Description |
|---|---:|---|
| `DEVFEAT_TURBO_QUEUE` | `0` | Turbo queue submission/completion rings supported. |
| `DEVFEAT_TURBO_DMA` | `1` | Device can initiate fabric DMA transactions. |
| `DEVFEAT_TURBO_TIMESTAMPS` | `2` | Timestamping supported for turbo operations. |
| `DEVFEAT_TURBO_PERF` | `3` | Performance counters implemented. |
| `DEVFEAT_TURBO_WATERMARK_IRQ` | `4` | FIFO watermark interrupts available. |

### Device Feature Fields

| Field | Word | Bits | Description |
|---|---:|---|---|
| `DEVFEAT_FIELD_RX_FIFO_DEPTH` | `0` | `7:0` | RX FIFO depth in entries (0 if not present). |
| `DEVFEAT_FIELD_TX_FIFO_DEPTH` | `0` | `15:8` | TX FIFO depth in entries (0 if not present). |
| `DEVFEAT_FIELD_DMA_CHANNELS` | `0` | `23:16` | DMA channel count (0 if not applicable). |
| `DEVFEAT_FIELD_TIMER_COUNT` | `0` | `31:24` | Timer counter count (0 if not applicable). |
| `DEVFEAT_FIELD_TIMESTAMP_BITS` | `1` | `7:0` | Timestamp width in bits (0 if not supported). |
| `DEVFEAT_FIELD_QUEUE_COUNT` | `1` | `15:8` | Turbo queue count (0 if none). |
| `DEVFEAT_FIELD_QUEUE_DEPTH` | `1` | `31:16` | Turbo queue ring depth (entries, 0 if not present). |

### Device Common CSR Register IDs

| Register | Reg ID | Access | Description |
|---|---:|---|---|
| `DEVCSR_ID` | `0x000` | `CSR_RO` | Device identification (class/vendor/device/revision encoding). |
| `DEVCSR_STATUS` | `0x001` | `CSR_RO` | Device status summary (busy/error flags). |
| `DEVCSR_CTRL` | `0x002` | `CSR_RW` | Device control (enable/reset). |
| `DEVCSR_MODE` | `0x003` | `CSR_RW` | Device personality/mode selection. |
| `DEVCSR_FEATURE0` | `0x004` | `CSR_RO` | Feature word 0 (mirrors descriptor feature_word0). |
| `DEVCSR_FEATURE1` | `0x005` | `CSR_RO` | Feature word 1 (mirrors descriptor feature_word1). |
| `DEVCSR_QUEUE_SUBMIT_BASE_LO` | `0x010` | `CSR_RW` | Turbo submission ring base (low 32). |
| `DEVCSR_QUEUE_SUBMIT_BASE_HI` | `0x011` | `CSR_RW` | Turbo submission ring base (high 32). |
| `DEVCSR_QUEUE_SUBMIT_MASK` | `0x012` | `CSR_RW` | Turbo submission ring mask (entries-1). |
| `DEVCSR_QUEUE_DOORBELL` | `0x013` | `CSR_WO` | Turbo submission doorbell. |
| `DEVCSR_QUEUE_COMP_BASE_LO` | `0x014` | `CSR_RW` | Turbo completion ring base (low 32). |
| `DEVCSR_QUEUE_COMP_BASE_HI` | `0x015` | `CSR_RW` | Turbo completion ring base (high 32). |
| `DEVCSR_QUEUE_COMP_MASK` | `0x016` | `CSR_RW` | Turbo completion ring mask (entries-1). |
| `DEVCSR_QUEUE_COMP_DOORBELL` | `0x017` | `CSR_RO` | Completion doorbell (device -> host pulse). |
| `DEVCSR_QUEUE_STATUS` | `0x018` | `CSR_RO` | Queue status (head/tail snapshot or device-specific). |
| `DEVCSR_PERF0` | `0x020` | `CSR_RO` | Performance counter 0 (device-specific meaning). |
| `DEVCSR_PERF1` | `0x021` | `CSR_RO` | Performance counter 1 (device-specific meaning). |

### Turbo Queue Submission Descriptor (V1)

- Format: `TURBO_SUBMIT_DESC_V1`, version `1`, size `32` bytes

| Field | Offset | Width (bytes) | Type | Description |
|---|---:|---:|---|---|
| `desc_version` | `0` | `2` | `u16` | Descriptor format version (must be 1 for v1.0). |
| `desc_size_dw` | `2` | `2` | `u16` | Descriptor size in 32-bit words (must be 8 for this format). |
| `queue_id` | `4` | `2` | `u16` | Queue identifier. |
| `opcode` | `6` | `2` | `u16` | Device-defined operation code. |
| `flags` | `8` | `4` | `u32` | Operation flags (reserved bits must be 0). |
| `tag` | `12` | `4` | `u32` | Opaque tag returned in the completion record. |
| `data_ptr` | `16` | `8` | `u64` | Pointer to payload or buffer (device-defined). |
| `data_len` | `24` | `4` | `u32` | Payload length in bytes (device-defined). |
| `data_stride` | `28` | `4` | `u32` | Payload stride in bytes (0=contiguous). |

### Turbo Queue Completion Record (V1)

- Format: `TURBO_COMP_REC_V1`, version `1`, size `16` bytes

| Field | Offset | Width (bytes) | Type | Description |
|---|---:|---:|---|---|
| `tag` | `0` | `4` | `u32` | Tag from the submission descriptor. |
| `status` | `4` | `2` | `u16` | Completion status code. |
| `ext_status` | `6` | `2` | `u16` | Optional extended status (device-defined). |
| `bytes_written` | `8` | `4` | `u32` | Optional byte count written (0 if unused). |
| `reserved0` | `12` | `4` | `u32` | Reserved; must be 0. |

### Turbo Queue Completion Status Codes

| Name | Value | Description |
|---|---:|---|
| `TURBO_STATUS_OK` | `0` | Success. |
| `TURBO_STATUS_INVALID` | `1` | Invalid/unsupported opcode or descriptor. |
| `TURBO_STATUS_FAULT` | `2` | Access fault or invalid pointer/length. |
| `TURBO_STATUS_BUSY` | `3` | Device busy or queue full. |
| `TURBO_STATUS_UNSUPPORTED` | `4` | Feature unsupported. |

## K) External Interfaces

### Legacy Z80 Bus Adapter Profiles

| Profile | Value | Description |
|---|---:|---|
| `LEGACY_RC2014` | `0` | RC2014-compatible bus timing profile. |
| `LEGACY_S100` | `1` | S-100-compatible bus timing profile. |

### Modern SoC External Profiles

| Profile | Value | Description |
|---|---:|---|
| `SOC_MEM_GENERIC` | `16` | Generic synchronous memory interface contract. |
| `SOC_PERIPH_GENERIC` | `17` | Generic peripheral interface contract. |

### Debug Transport

- Minimum: `UART`

## L) Common Interfaces

| Interface | Value | Description |
|---|---:|---|
| `fabric_if` | `0` | Fabric request/response channel carrying transactions and attributes. |
| `csr_if` | `1` | CSR access interface for control/status registers. |
| `irq_if` | `2` | Interrupt delivery interface for INT/NMI and routed IRQs. |
| `dbg_if` | `3` | Debug control interface (halt/run/step/trace). |
| `cai_if` | `4` | Accelerator/peripheral queue interface for CAI devices. |

## M) Z90 Fast-Path ISA (Opcode Pages)

### Opcode Pages

| Page | Prefix Bytes | Description |
|---|---|---|
| `Z90_OPPAGE_P0` | `0xed 0xf0` | Page 0 (register/ALU/system control/CAI). |
| `Z90_OPPAGE_P1` | `0xed 0xf1` | Page 1 (memory/addressing/atomics). |

### Page0 Majors

| Name | Value | Description |
|---|---:|---|
| `Z90_P0_MAJOR_REG` | `0` | Register move/exchange. |
| `Z90_P0_MAJOR_ALU` | `1` | Integer ALU ops on X registers. |
| `Z90_P0_MAJOR_SYS` | `15` | System control (MODEUP/RETMD/CAI). |

### Page0 Subops

| Name | Major | Value | Description |
|---|---|---:|---|
| `Z90_P0_SUB_MOV` | `Z90_P0_MAJOR_REG` | `0` | MOV Xd, Xs. |
| `Z90_P0_SUB_XCHG` | `Z90_P0_MAJOR_REG` | `1` | XCHG Xd, Xs. |
| `Z90_P0_SUB_ADD` | `Z90_P0_MAJOR_ALU` | `0` | ADD Xd, Xs. |
| `Z90_P0_SUB_SUB` | `Z90_P0_MAJOR_ALU` | `1` | SUB Xd, Xs. |
| `Z90_P0_SUB_AND` | `Z90_P0_MAJOR_ALU` | `2` | AND Xd, Xs. |
| `Z90_P0_SUB_OR` | `Z90_P0_MAJOR_ALU` | `3` | OR Xd, Xs. |
| `Z90_P0_SUB_XOR` | `Z90_P0_MAJOR_ALU` | `4` | XOR Xd, Xs. |
| `Z90_P0_SUB_CMP` | `Z90_P0_MAJOR_ALU` | `5` | CMP Xd, Xs (flags only). |
| `Z90_P0_SUB_MODEUP` | `Z90_P0_MAJOR_SYS` | `0` | MODEUP(target_tier_u8, entry_vector_u16). rs selects ladder (0=Z80-derived ladder). |
| `Z90_P0_SUB_RETMD` | `Z90_P0_MAJOR_SYS` | `1` | RETMD(). |
| `Z90_P0_SUB_CAI_CFG` | `Z90_P0_MAJOR_SYS` | `8` | CAI_CFG (implementation-defined mapping onto cai_if host registers). |
| `Z90_P0_SUB_CAI_SUBMIT` | `Z90_P0_MAJOR_SYS` | `9` | CAI_SUBMIT rings the CAI submission doorbell. |

### Page1 Ops

| Name | Value | Description |
|---|---:|---|
| `Z90_P1_OP_LD16` | `1` | LD16 Xd, [base + index + disp8]. |
| `Z90_P1_OP_ST16` | `2` | ST16 [base + index + disp8], Xd. |
| `Z90_P1_OP_LEA` | `3` | LEA Xd, [base + index + disp8]. |
| `Z90_P1_OP_CAS16` | `4` | CAS16 Xd, [base + disp8], Xs (Xd expected/old, Xs desired; Z90.Z=success). |

## N) Numeric Formats

| Name | Value | Width | Exp | Frac | Bias | Description |
|---|---:|---:|---:|---:|---:|---|
| `FMT_BINARY16` | `0` | `16` | `5` | `10` | `15` | IEEE 754 binary16 (half). |
| `FMT_BFLOAT16` | `1` | `16` | `8` | `7` | `127` | bfloat16. |
| `FMT_BINARY32` | `2` | `32` | `8` | `23` | `127` | IEEE 754 binary32 (single). |
| `FMT_BINARY64` | `3` | `64` | `11` | `52` | `1023` | IEEE 754 binary64 (double). |

### Rounding Modes

| Name | Value | Mnemonic | Description |
|---|---:|---|---|
| `RND_RN` | `0` | `RN` | Round to nearest, ties to even. |
| `RND_RZ` | `1` | `RZ` | Round toward zero. |
| `RND_RP` | `2` | `RP` | Round toward +infinity. |
| `RND_RM` | `3` | `RM` | Round toward -infinity. |

