# OS Loader Framework

This folder contains helper scripts to assemble bootable memory images without
shipping copyrighted OS binaries.

## mk_os_image.py

Build a flat memory image by placing binary segments at fixed addresses.

Example:

```bash
python source/os/common/loader/mk_os_image.py \
  --size 65536 \
  --entry 0x0100 \
  --segment build/cpm22_system.bin@0x0100 \
  --segment build/cpm22_bios.bin@0xE000 \
  --bsp build/carbonz80_bsp.bin@0xFF00 \
  --out build/cpm22_mem.bin \
  --map-out build/cpm22_mem.map
```

The resulting `*.bin` image can be injected into the simulator or HDL testbench
RAM before releasing reset.
