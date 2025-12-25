# SPEC_IRQ (v1.0)

Purpose
- Define IRQ routing encoding and PIC acknowledgement rules.

Versioning
- Version format: major.minor.
- Major mismatch: reject and fail boot.
- Minor greater than supported: reject and fail boot.
- Minor lower or equal: accept; reserved bits remain reserved.

Binary layout
- IRQ routing entries use JC_BDT_IRQ_ROUTE_V1 (see SPEC_BDT).
- Endianness: little-endian for multi-byte fields.

Routing encoding
- domain_id identifies the PIC instance (BDT instance_id for DEVCLASS_PIC).
- irq_line is the PIC input line number for that domain.
- Vector numbers are not encoded in the BDT; they are determined by the PIC.

IRQ flags
- IRQ_FLAG_EDGE = bit 0 (1=edge, 0=level)
- IRQ_FLAG_ACTIVE_HIGH = bit 1 (1=active high, 0=active low)

Acknowledgement/EOI
- An IRQ is cleared when its source condition is cleared.
- No explicit EOI register is required for v1.

Invariants
- irq_line values are zero-based within a PIC domain.
- flags bits outside 0-1 must be 0.

Failure semantics
- Unknown domain_id or irq_line is fatal during device binding.
