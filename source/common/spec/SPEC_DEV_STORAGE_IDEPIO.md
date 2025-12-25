# SPEC_DEV_STORAGE_IDEPIO (v1.0)

Purpose
- Define the minimum IDE/CF PIO register ABI for CarbonStorage.

Versioning
- Version format: major.minor.
- Major mismatch: reject and fail boot.
- Minor greater than supported: reject and fail boot.
- Minor lower or equal: accept; reserved bits remain reserved.

Binary layout
- Register width: 8 bits.
- Access: I/O port space at the device's I/O base.

Register map (compatibility)
- DATA @+0
- ERROR (RO) / FEATURES (WO) @+1
- SECTOR_COUNT @+2
- SECTOR_NUMBER (LBA0) @+3
- CYLINDER_LOW (LBA1) @+4
- CYLINDER_HIGH (LBA2) @+5
- DRIVE_HEAD @+6
- STATUS (RO) / COMMAND (WO) @+7

Required commands
- IDENTIFY (0xEC)
- READ SECTOR(S) (0x20)
- WRITE SECTOR(S) (0x30)

STATUS bits
- bit 0: ERR
- bit 3: DRQ
- bit 4: DSC
- bit 6: DRDY
- bit 7: BSY

ERROR bits
- bit 2: ABRT (command aborted)

Init/reset sequence
- Write DRIVE_HEAD with bit6=1 to enable LBA mode.
- Poll STATUS until BSY=0 and DRDY=1.
- Issue IDENTIFY and confirm DRQ.

Timeout rules
- BIOS uses the monotonic tick to enforce command deadlines.
- Timeout value is reported in BDT caps1 bits 31:0 (ticks).

Invariants
- sector_size must be at least 512 bytes (BDT field block_sector_size).
- LBA mode is required; CHS is not used in v1.

Failure semantics
- If STATUS.BSY remains 1 past the timeout, the command fails with JC_E_DEV_IO_TIMEOUT.
- If STATUS.ERR is set, the command fails with JC_E_DEV_IO_ERROR.
