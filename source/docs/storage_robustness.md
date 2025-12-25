# Storage Robustness Policy (v1.7)

Purpose
- Define deterministic retry, backoff, and bad-sector handling for CarbonStorage.

Policy (BIOS block layer)
- Max retries: `JC_BLOCK_RETRY_MAX` (2). Total attempts = 1 + max retries.
- Backoff: exponential tick delay starting at `JC_BLOCK_RETRY_BACKOFF_TICKS` (1).
- Bad sectors: after persistent I/O timeout or error, the LBA is recorded and
  subsequent accesses return the stored error (no remap in v1).

Determinism
- Retry and backoff are fixed constants, not adaptive.
- Bad-sector list is a fixed-size ring of `JC_BLOCK_BAD_SECTOR_MAX` (16) entries.

Failure semantics
- `JC_E_DEV_IO_TIMEOUT` retries are attempted; failure returns timeout.
- `JC_E_DEV_IO_ERROR` is returned immediately and recorded as bad.
- Other errors are returned without retry and do not mark the sector.
