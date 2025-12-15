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

