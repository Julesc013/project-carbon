# SPEC_CAI (v1.0)

Purpose
- Define the Carbon Accelerator Interface (CAI) queue and descriptor ABI.

Versioning
- Version format: major.minor.
- Major mismatch: reject and fail submission.
- Minor greater than supported: reject and fail submission.
- Minor lower or equal: accept; reserved fields remain reserved.

Binary layout
- Endianness: little-endian for all multi-byte fields.
- Alignment: 4-byte aligned descriptors.

Submission descriptor (JC_CAI_SUBMIT_DESC_V1, 64 bytes)
- desc_version: u16 @0 (must be 1)
- desc_size_dw: u16 @2 (must be 16)
- opcode: u32 @4
- flags: u32 @8 (reserved bits must be 0)
- context_id: u16 @12
- operand_count: u16 @14
- tag: u32 @16
- opcode_group: u8 @20
- format_primary: u8 @21
- format_aux: u8 @22
- format_flags: u8 @23 (must be 0)
- operands_ptr: u64 @24
- result_ptr: u64 @32
- result_len: u32 @40
- result_stride: u32 @44
- tensor_desc_ptr: u64 @48
- tensor_desc_len: u16 @56
- tensor_rank: u8 @58
- tensor_desc_flags: u8 @59
- reserved2: u32 @60 (must be 0)

Operand descriptor (JC_CAI_OPERAND_DESC_V1, 32 bytes)
- ptr: u64 @0
- len: u32 @8
- stride: u32 @12
- flags: u32 @16
- reserved0: u32 @20 (must be 0)
- reserved1: u64 @24 (must be 0)

Tensor descriptor (JC_CAI_TENSOR_DESC_V1, 64 bytes)
- desc_version: u16 @0 (must be 1)
- desc_size_dw: u16 @2 (must be 16)
- rank: u8 @4
- elem_format: u8 @5
- reserved0: u16 @6 (must be 0)
- flags: u32 @8
- shape0: u32 @12
- shape1: u32 @16
- shape2: u32 @20
- shape3: u32 @24
- stride0: u32 @28
- stride1: u32 @32
- stride2: u32 @36
- stride3: u32 @40
- reserved1: u32 @44 (must be 0)
- reserved2: u64 @48 (must be 0)
- reserved3: u64 @56 (must be 0)

Completion record (JC_CAI_COMP_REC_V1, 16 bytes)
- tag: u32 @0
- status: u16 @4
- ext_status: u16 @6
- bytes_written: u32 @8
- reserved0: u32 @12 (must be 0)

Opcode groups
- AM95_SCALAR = 0
- AM95_VECTOR = 1
- AM95_TENSOR = 2
- DMA_COPY = 3
- DMA_FILL = 4
- UART_STREAM = 5

Completion status codes
- CAI_STATUS_OK = 0
- CAI_STATUS_INVALID_OP = 1
- CAI_STATUS_FAULT = 2
- CAI_STATUS_TIMEOUT = 3
- CAI_STATUS_UNSUPPORTED = 4

Invariants
- Producer must make descriptors visible before ringing the doorbell.
- Completion ring writes must be visible before the completion is observed by software.
- Reserved fields must be 0.

Failure semantics
- Invalid descriptor versions or sizes result in CAI_STATUS_INVALID_OP.
- Access faults in operand/result buffers result in CAI_STATUS_FAULT.
