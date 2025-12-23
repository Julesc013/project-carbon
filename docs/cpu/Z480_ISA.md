# Z480 ISA v1 (Minimal Subset)

This document defines the minimal Z480 ISA subset implemented by `z480_core.sv`.
The encoding is fixed 32-bit and MIPS-like.

## Encoding

All instruction words are 32 bits. Memory is little-endian.

### R-type (SPECIAL, op = 0x00)

```
31:26  op     (0x00)
25:21  rs
20:16  rt
15:11  rd
10:6   shamt  (0 in v1)
5:0    funct
```

### I-type

```
31:26  op
25:21  rs
20:16  rt
15:0   imm16  (sign-extended)
```

### J-type

```
31:26  op
25:0   imm26
```

Target address = `{PC[63:28], imm26, 2'b00}`.

## Registers

- 32 general-purpose registers (`r0`..`r31`), 64-bit each.
- `r0` is hardwired to zero.
- `PC` is 64-bit.

## Implemented instructions

### R-type (op = 0x00)

| funct | mnemonic | semantics |
|---:|---|---|
| 0x00 | NOP | no-op |
| 0x08 | JR  | `PC <- rs` |
| 0x20 | ADD | `rd <- rs + rt` |
| 0x22 | SUB | `rd <- rs - rt` |
| 0x24 | AND | `rd <- rs & rt` |
| 0x25 | OR  | `rd <- rs | rt` |
| 0x26 | XOR | `rd <- rs ^ rt` |

### I-type (opcodes)

| op | mnemonic | semantics |
|---:|---|---|
| 0x08 | ADDI | `rt <- rs + sext(imm16)` |
| 0x04 | BEQ  | if `rs == rt` then `PC <- PC + (sext(imm16) << 2)` |
| 0x05 | BNE  | if `rs != rt` then `PC <- PC + (sext(imm16) << 2)` |

### Loads / stores (I-type)

All load/store instructions use `addr = rs + sext(imm16)`.

| op | mnemonic | size | notes |
|---:|---|---|---|
| 0x20 | LDB | 1 | sign-extended |
| 0x21 | LDH | 2 | sign-extended, 2-byte aligned |
| 0x23 | LDW | 4 | sign-extended, 4-byte aligned |
| 0x24 | LDD | 4 | alias of LDW in v1 |
| 0x25 | LDQ | 8 | 8-byte aligned, two 32-bit beats |
| 0x28 | STB | 1 | |
| 0x29 | STH | 2 | 2-byte aligned |
| 0x2B | STW | 4 | 4-byte aligned |
| 0x2C | STD | 4 | alias of STW in v1 |
| 0x2D | STQ | 8 | 8-byte aligned, two 32-bit beats |

Misaligned accesses trap with `ALIGN`.

### CSR access

| op | mnemonic | semantics |
|---:|---|---|
| 0x30 | CSRR | `rt <- CSR[rs + sext(imm16)]` |
| 0x31 | CSRW | `CSR[rs + sext(imm16)] <- rt` (privileged checks apply) |

### Other

| op | mnemonic | semantics |
|---:|---|---|
| 0x02 | J | jump (J-type) |
| 0x03 | JAL | link to `r31`, then J |
| 0x32 | MODEUP | traps with `MODEUP_INVALID` in v1 |
| 0x33 | RETMD | traps with `MODEUP_INVALID` in v1 |
| 0x34 | FENCE | no-op in v1 |
| 0x35 | FENCE_IO | no-op in v1 |
| 0x36 | RFE | return from trap (restore PC/priv) |

## Traps

The core raises deterministic traps for:
- Illegal instruction (`ILLEGAL`)
- Misaligned access (`ALIGN`)
- CSR access faults (`CSR`)
- Fabric errors (`BUS`)
- Interrupt delivery (`IRQ`)
- `MODEUP/RETMD` use (`MODEUP_INVALID`)

Trap entry vectors to the appropriate privilege base address and updates `CAUSE`, `EPC`,
and `BADADDR` CSRs.
