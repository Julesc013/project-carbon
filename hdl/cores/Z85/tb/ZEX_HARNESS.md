# ZEX Harness (Z85)

The Z85 testbench includes an optional ZEXALL/ZEXDOC runner. It is disabled by
default and only runs when a ZEX image is provided.

## How it works

- 0x0000 jumps to a small boot stub.
- 0x0005 contains a BDOS stub that prints by `OUT (0),A`. A byte of `0xFF`
  signals completion.
- The boot stub performs `MODEUP` to P2 and jumps to the ZEX entry address
  (default `0x0100`).

## Input formats

- `+zex_hex=<path>` uses `$readmemh` (ASCII hex bytes).
- `+zex_bin=<path>` uses `$readmemb` (ASCII binary bytes).

## Running

Build the optional testbench:

```sh
make -C hdl/sim tb_z85_zex
```

Run with plusargs (examples):

```sh
vvp hdl/sim/build/tb_z85_zex.vvp +zex_hex=path/to/zex.hex +zex_entry=0100 +zex_timeout=200000
```

```sh
hdl/sim/build/verilator/tb_z85_zex/tb_z85_zex +zex_hex=path/to/zex.hex +zex_entry=0100 +zex_timeout=200000
```

## Pass/fail

- Pass: output is printed and the test ends with `tb_z85: ZEX PASS`.
- Skip: `tb_z85: ZEX SKIP` when no ZEX image is provided.
- Fail: timeout or fatal error.
