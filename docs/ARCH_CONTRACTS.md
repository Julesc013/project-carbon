# Project Carbon — Frozen Architecture Contracts (v1.0)

_AUTO-GENERATED from `hdl/spec/*.yaml` by `hdl/tools/gen_specs.py`._

## A) Compatibility Tier Ladders

### TIER_LADDER_Z80 (Z80-derived compatibility ladder.)

- Reset default: `P0`
- Upgrade rule: `target_tier > current_tier`
- Downgrade rule: `only via RETMD`

| Tier | Value | Label | Strict | Turbo |
|---:|---:|---|:---:|:---:|
| `P0` | `0` | `8080` | true |  |
| `P1` | `1` | `8085` | true |  |
| `P2` | `2` | `z80` | true |  |
| `P3` | `3` | `z180` | true |  |
| `P4` | `4` | `z280` | true |  |
| `P5` | `5` | `z380` | true |  |
| `P6` | `6` | `eZ80` | true |  |
| `P7` | `7` | `TURBO_UNLIMITED` |  | true |

### TIER_LADDER_X86 (x86-derived compatibility ladder.)

- Reset default: `P0`
- Upgrade rule: `target_tier > current_tier`
- Downgrade rule: `only via RETMD`

| Tier | Value | Label | Strict | Turbo |
|---:|---:|---|:---:|:---:|
| `P0` | `0` | `8086/8087` | true |  |
| `P1` | `1` | `286/287` | true |  |
| `P2` | `2` | `386/387` | true |  |
| `P3` | `3` | `486/487` | true |  |
| `P4` | `4` | `586/587` | true |  |
| `P5` | `5` | `686/687` | true |  |
| `P6` | `6` | `786/787` | true |  |
| `P7` | `7` | `TURBO_UNLIMITED` |  | true |

### TIER_LADDER_AMD_FPU (AMD-derived FPU compatibility ladder.)

- Reset default: `P0`
- Upgrade rule: `target_tier > current_tier`
- Downgrade rule: `only via RETMD`

| Tier | Value | Label | Strict | Turbo |
|---:|---:|---|:---:|:---:|
| `P0` | `0` | `am9511` | true |  |
| `P1` | `1` | `am9512` | true |  |
| `P7` | `7` | `TURBO_UNLIMITED` |  | true |

## B) Mode Switching Contract

### Instructions

| Instruction | Signature | Description |
|---|---|---|
| `MODEUP` | `MODEUP(target_tier, entry_vector)` | Upgrade-only transition into a higher compatibility tier. |
| `RETMD` | `RETMD()` | Return from mode (the only architectural tier downgrade mechanism). |

### MODEFLAGS

- Width: `8` bits

| Name | Bit | Reset | Description |
|---|---:|---:|---|
| `MODEFLAG_STRICT` | `0` | `1` | When 1, turbo/extension behaviors are disabled regardless of tier. |
| `MODEFLAG_INTMASK` | `1` | `0` | Architectural interrupt mask hint; when 1, mask interrupts (implementation-defined sources). |

### MODESTACK

- Minimum depth: `4`
- Recommended depth: `16`

## C) Discovery / CPUID / CAPS

- Endianness: `little`
- Leaf return words: `4` x `32`-bit
- Unknown leaf behavior: `return_zeros`

### CPUID Leaf IDs

| Leaf | ID | Description |
|---|---:|---|
| `CPUID_LEAF_VENDOR` | `0x00000000` | Maximum standard leaf and vendor string. |
| `CPUID_LEAF_ID` | `0x00000001` | Vendor ID, family ID, model ID, and stepping. |
| `CPUID_LEAF_TIERS` | `0x00000002` | Active tier ladder and tier limits. |
| `CPUID_LEAF_FEATURES0` | `0x00000003` | Base feature bitmap (bits 0..127 across words 0..3). |
| `CPUID_LEAF_CACHE0` | `0x00000010` | Cache descriptor 0 (if present). |
| `CPUID_LEAF_TOPOLOGY` | `0x00000011` | Core/thread topology descriptor. |
| `CPUID_LEAF_ACCEL0` | `0x00000020` | Accelerator presence descriptor 0. |
| `CPUID_LEAF_ERRATA0` | `0x00000030` | Errata bitmap 0 (bits 0..127 across words 0..3). |

### Feature Bits

| Feature | Bit | Description |
|---|---:|---|
| `FEAT_MODE_SWITCH` | `0` | MODEUP/RETMD mode switching contract implemented. |
| `FEAT_CSR_NAMESPACE` | `1` | Carbon CSR namespace and access model implemented. |
| `FEAT_FABRIC` | `2` | Carbon internal fabric transaction contract implemented. |
| `FEAT_CAI` | `3` | Carbon Accelerator Interface (CAI) implemented. |
| `FEAT_CPUID` | `4` | CPUID instruction transport implemented (eZ90 P7). |
| `FEAT_CAPS` | `5` | CAPS transport implemented (Z85/Z90). |
| `FEAT_AM9513` | `6` | Am9513-class accelerator present. |
| `FEAT_IOMMU_HOOKS` | `7` | IOMMU integration hooks for accelerators/fabric present. |

### Example CPUID Leaf Table (IDs)

| Leaf ID | Name |
|---:|---|
| `0x00000000` | `CPUID_LEAF_VENDOR` |
| `0x00000001` | `CPUID_LEAF_ID` |
| `0x00000002` | `CPUID_LEAF_TIERS` |
| `0x00000003` | `CPUID_LEAF_FEATURES0` |

## D) CSR Namespace + Register Model

- Unknown CSR behavior: `trap`

| CSR | Address | Access | Min Priv | Description |
|---|---:|---|---|---|
| `CSR_ID` | `0x00000000` | `CSR_RO` | `PRIV_U` | Read-only identification register (implementation-defined encoding). |
| `CSR_TIER` | `0x00000001` | `CSR_RW` | `PRIV_S` | Current tier within the active ladder; tier changes use MODEUP/RETMD. |
| `CSR_MODEFLAGS` | `0x00000002` | `CSR_RW` | `PRIV_S` | Architectural MODEFLAGS bitfield (see mode_switch spec). |
| `CSR_TIME` | `0x00000010` | `CSR_RO` | `PRIV_U` | Cycle counter low word (or full 64-bit counter when read as 64-bit). |
| `CSR_TIME_HI` | `0x00000011` | `CSR_RO` | `PRIV_U` | Cycle counter high word (when exposed as 2x32-bit). |
| `CSR_CAUSE` | `0x00000020` | `CSR_RO` | `PRIV_S` | Trap cause metadata (encoding defined by trap/exception architecture). |
| `CSR_EPC` | `0x00000021` | `CSR_RW` | `PRIV_S` | Exception program counter (trap return address). |
| `CSR_IE` | `0x00000030` | `CSR_RW` | `PRIV_S` | Interrupt enable bits. |
| `CSR_IP` | `0x00000031` | `CSR_RO` | `PRIV_S` | Interrupt pending bits. |
| `CSR_TRACE_CTL` | `0x00000040` | `CSR_RW` | `PRIV_S` | Trace control register (trace on/off and mode bits). |
| `CSR_Z90_MMU_WIN0_BASE` | `0x00a10000` | `CSR_RW` | `PRIV_S` | Z90 MMU/window register 0 base address (register-only placeholder). |
| `CSR_Z90_MMU_WIN0_MASK` | `0x00a10004` | `CSR_RW` | `PRIV_S` | Z90 MMU/window register 0 mask/limit (register-only placeholder). |
| `CSR_Z90_MMU_WIN1_BASE` | `0x00a10008` | `CSR_RW` | `PRIV_S` | Z90 MMU/window register 1 base address (register-only placeholder). |
| `CSR_Z90_MMU_WIN1_MASK` | `0x00a1000c` | `CSR_RW` | `PRIV_S` | Z90 MMU/window register 1 mask/limit (register-only placeholder). |
| `CSR_Z90_CACHE_CTL` | `0x00a10010` | `CSR_RW` | `PRIV_S` | Z90 cache control hooks (register-only placeholder; no cache logic implied). |
| `CSR_Z90_ATOMIC_CTL` | `0x00a10014` | `CSR_RW` | `PRIV_S` | Z90 atomic enable/control (register-only placeholder). |
| `CSR_Z90_ATOMIC_STATUS` | `0x00a10018` | `CSR_RO` | `PRIV_S` | Z90 atomic status (register-only placeholder). |
| `CSR_AM9513_ID` | `0x00700000` | `CSR_RO` | `PRIV_U` | Am9513 identification register (implementation-defined encoding). |
| `CSR_AM9513_CTRL` | `0x00700004` | `CSR_RW` | `PRIV_S` | Am9513 global control (v1.0: enable). |
| `CSR_AM9513_STATUS` | `0x00700008` | `CSR_RO` | `PRIV_U` | Am9513 global status (busy, pending work, last fault). |
| `CSR_AM9513_MODE` | `0x0070000c` | `CSR_RW` | `PRIV_S` | Default personality/mode select (P0/P1/P7) for non-CAI paths. |
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

## E) Fabric Transaction Contract

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
| `FABRIC_ATTR_CACHEABLE` | `0` | `1` | 1=cacheable, 0=uncacheable. |
| `FABRIC_ATTR_ORDERED` | `1` | `1` | 1=ordered, 0=normal ordering. |
| `FABRIC_ATTR_IO_SPACE` | `2` | `1` | 1=IO space, 0=memory space. |
| `FABRIC_ATTR_ACQUIRE` | `3` | `1` | Acquire semantics (for synchronization). |
| `FABRIC_ATTR_RELEASE` | `4` | `1` | Release semantics (for synchronization). |
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

## F) Carbon Accelerator Interface (CAI)

### Submission Descriptor (V1)

- Format: `CAI_SUBMIT_DESC_V1`, version `1`, size `64` bytes

| Field | Offset | Width (bytes) | Type | Description |
|---|---:|---:|---|---|
| `desc_version` | `0` | `2` | `u16` | Descriptor format version (must be 1 for v1.0). |
| `desc_size_dw` | `2` | `2` | `u16` | Descriptor size in 32-bit words (must be 16 for this format). |
| `opcode` | `4` | `4` | `u32` | Operation code. |
| `flags` | `8` | `4` | `u32` | Operation flags (reserved bits must be 0). |
| `context_id` | `12` | `2` | `u16` | Context identifier. |
| `operand_count` | `14` | `2` | `u16` | Number of operand descriptors in the operand list. |
| `tag` | `16` | `4` | `u32` | Opaque tag returned in the completion record. |
| `reserved0` | `20` | `4` | `u32` | Reserved; must be 0. |
| `operands_ptr` | `24` | `8` | `u64` | Pointer to an array of operand descriptors. |
| `result_ptr` | `32` | `8` | `u64` | Pointer to the result buffer. |
| `result_len` | `40` | `4` | `u32` | Result length in bytes (or elements, opcode-defined). |
| `result_stride` | `44` | `4` | `u32` | Stride in bytes between result elements (0=contiguous). |
| `reserved1` | `48` | `8` | `u64` | Reserved; must be 0. |
| `reserved2` | `56` | `8` | `u64` | Reserved; must be 0. |

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
operands_ptr: 268435456
result_ptr: 536870912
result_len: 256
result_stride: 0
```

## G) Z90 Fast-Path ISA (Opcode Pages)

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

## H) Numeric Formats

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

