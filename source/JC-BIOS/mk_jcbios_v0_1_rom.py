#!/usr/bin/env python3
"""
Build the JC-BIOS v0.1 boot ROM for CarbonZ* platforms.

This emits a 256-byte 8080-compatible ROM stub plus a RAM payload with:
- reset entry, stack init, interrupts disabled
- minimal CAPS capability probe into a fixed RAM struct
- VT100-compatible console output (UART TX only)
- deterministic banner and monitor stub
The RAM payload is linked at BIOS_ENTRY and should be loaded with --load-addr.
"""

from __future__ import annotations

import argparse
from pathlib import Path
from typing import Dict, List, Tuple, Union

ByteLike = Union[int, bytes, bytearray]


# Hardware assumptions (v0.1, CarbonZ* simulation mapping).
ROM_SIZE = 256
BIOS_ENTRY = 0x0200
CAPSET_BASE = 0x0100
UART_DATA = 0xF100
UART_CTRL = 0xF108
# CAPS is mapped to low I/O space for P0-safe IN/OUT access.
CAPS_BASE_PORT = 0x0020
CAPS_INDEX_PORT = CAPS_BASE_PORT + 0x00
CAPS_DATA0_PORT = CAPS_BASE_PORT + 0x04
CAPS_DATA1_PORT = CAPS_BASE_PORT + 0x08


class Asm8080:
    """Minimal 8080 assembler helper with labels and fixups."""

    def __init__(self, origin: int = 0x0000) -> None:
        self.origin = origin
        self.buf = bytearray()
        self.labels: Dict[str, int] = {}
        self.fixups: List[Tuple[int, str]] = []

    @property
    def addr(self) -> int:
        return self.origin + len(self.buf)

    def label(self, name: str) -> None:
        if name in self.labels:
            raise ValueError(f"duplicate label: {name}")
        self.labels[name] = self.addr

    def emit(self, *values: ByteLike) -> None:
        for v in values:
            if isinstance(v, (bytes, bytearray)):
                self.buf.extend(v)
                continue
            if not 0 <= v <= 0xFF:
                raise ValueError(f"byte out of range: {v}")
            self.buf.append(v)

    def emit_u16(self, value: int) -> None:
        if not 0 <= value <= 0xFFFF:
            raise ValueError(f"u16 out of range: {value}")
        self.emit(value & 0xFF, (value >> 8) & 0xFF)

    def emit_u16_or_label(self, value: Union[int, str]) -> None:
        if isinstance(value, str):
            self.fixups.append((len(self.buf), value))
            self.emit(0x00, 0x00)
        else:
            self.emit_u16(value)

    def resolve(self) -> None:
        for offset, label in self.fixups:
            if label not in self.labels:
                raise ValueError(f"unknown label: {label}")
            addr = self.labels[label]
            self.buf[offset] = addr & 0xFF
            self.buf[offset + 1] = (addr >> 8) & 0xFF

    def finish(self) -> bytes:
        self.resolve()
        return bytes(self.buf)

    def build(self, size: int) -> bytes:
        self.resolve()
        if len(self.buf) > size:
            raise ValueError(f"ROM too large: {len(self.buf)} bytes (max {size})")
        self.buf.extend([0x00] * (size - len(self.buf)))
        return bytes(self.buf)

    # 8080 instruction helpers.
    def di(self) -> None:
        self.emit(0xF3)

    def hlt(self) -> None:
        self.emit(0x76)

    def ret(self) -> None:
        self.emit(0xC9)

    def rz(self) -> None:
        self.emit(0xC8)

    def jmp(self, target: Union[int, str]) -> None:
        self.emit(0xC3)
        self.emit_u16_or_label(target)

    def jnz(self, target: Union[int, str]) -> None:
        self.emit(0xC2)
        self.emit_u16_or_label(target)

    def jz(self, target: Union[int, str]) -> None:
        self.emit(0xCA)
        self.emit_u16_or_label(target)

    def jc(self, target: Union[int, str]) -> None:
        self.emit(0xDA)
        self.emit_u16_or_label(target)

    def call(self, target: Union[int, str]) -> None:
        self.emit(0xCD)
        self.emit_u16_or_label(target)

    def lxi(self, rp: str, value: Union[int, str]) -> None:
        op = {"b": 0x01, "d": 0x11, "h": 0x21, "sp": 0x31}.get(rp.lower())
        if op is None:
            raise ValueError(f"invalid LXI register pair: {rp}")
        self.emit(op)
        self.emit_u16_or_label(value)

    def inx(self, rp: str) -> None:
        op = {"b": 0x03, "d": 0x13, "h": 0x23, "sp": 0x33}.get(rp.lower())
        if op is None:
            raise ValueError(f"invalid INX register pair: {rp}")
        self.emit(op)

    def dcx(self, rp: str) -> None:
        op = {"b": 0x0B, "d": 0x1B, "h": 0x2B, "sp": 0x3B}.get(rp.lower())
        if op is None:
            raise ValueError(f"invalid DCX register pair: {rp}")
        self.emit(op)

    def mvi(self, reg: str, value: int) -> None:
        op = {
            "b": 0x06,
            "c": 0x0E,
            "d": 0x16,
            "e": 0x1E,
            "h": 0x26,
            "l": 0x2E,
            "m": 0x36,
            "a": 0x3E,
        }.get(reg.lower())
        if op is None:
            raise ValueError(f"invalid MVI register: {reg}")
        self.emit(op, value & 0xFF)

    def mov(self, dst: str, src: str) -> None:
        reg = {"b": 0, "c": 1, "d": 2, "e": 3, "h": 4, "l": 5, "m": 6, "a": 7}
        if dst.lower() not in reg or src.lower() not in reg:
            raise ValueError(f"invalid MOV registers: {dst},{src}")
        self.emit(0x40 | (reg[dst.lower()] << 3) | reg[src.lower()])

    def stax(self, rp: str) -> None:
        op = {"b": 0x02, "d": 0x12}.get(rp.lower())
        if op is None:
            raise ValueError(f"invalid STAX register pair: {rp}")
        self.emit(op)

    def lda(self, addr: Union[int, str]) -> None:
        self.emit(0x3A)
        self.emit_u16_or_label(addr)

    def sta(self, addr: Union[int, str]) -> None:
        self.emit(0x32)
        self.emit_u16_or_label(addr)

    def ora(self, reg: str) -> None:
        op = {"b": 0xB0, "c": 0xB1, "d": 0xB2, "e": 0xB3, "h": 0xB4, "l": 0xB5, "m": 0xB6, "a": 0xB7}.get(reg.lower())
        if op is None:
            raise ValueError(f"invalid ORA register: {reg}")
        self.emit(op)

    def xra(self, reg: str) -> None:
        op = {"b": 0xA8, "c": 0xA9, "d": 0xAA, "e": 0xAB, "h": 0xAC, "l": 0xAD, "m": 0xAE, "a": 0xAF}.get(reg.lower())
        if op is None:
            raise ValueError(f"invalid XRA register: {reg}")
        self.emit(op)

    def ani(self, value: int) -> None:
        self.emit(0xE6, value & 0xFF)

    def cpi(self, value: int) -> None:
        self.emit(0xFE, value & 0xFF)

    def adi(self, value: int) -> None:
        self.emit(0xC6, value & 0xFF)

    def dcr(self, reg: str) -> None:
        op = {"b": 0x05, "c": 0x0D, "d": 0x15, "e": 0x1D, "h": 0x25, "l": 0x2D, "m": 0x35, "a": 0x3D}.get(reg.lower())
        if op is None:
            raise ValueError(f"invalid DCR register: {reg}")
        self.emit(op)

    def rrc(self) -> None:
        self.emit(0x0F)

    def out(self, port: int) -> None:
        self.emit(0xD3, port & 0xFF)

    def inp(self, port: int) -> None:
        self.emit(0xDB, port & 0xFF)

    def db(self, data: Union[str, bytes, bytearray, int]) -> None:
        if isinstance(data, int):
            self.emit(data & 0xFF)
            return
        if isinstance(data, str):
            data = data.encode("ascii")
        self.emit(data)


def emit_rom_stub(asm: Asm8080) -> None:
    """ROM stub: minimal reset path that jumps into the RAM BIOS body."""
    asm.label("reset_stub")
    asm.di()
    asm.lxi("sp", 0x01FF)
    asm.jmp(BIOS_ENTRY)


def emit_reset(asm: Asm8080) -> None:
    """Reset entry: disable interrupts, init stack/UART, then boot JC-BIOS."""
    asm.label("reset")
    asm.di()
    asm.lxi("sp", 0x01FF)
    asm.lxi("d", UART_DATA)
    asm.mvi("a", 0x01)
    asm.sta(UART_CTRL)
    asm.call("caps_probe")
    asm.call("boot_banner")
    asm.call("monitor_stub")
    asm.hlt()
    asm.jmp("reset")


def emit_caps_probe(asm: Asm8080) -> None:
    """Probe CAPS (if present) and normalize into the in-memory capset."""
    asm.label("caps_probe")
    asm.lxi("h", CAPSET_BASE)
    asm.mvi("a", 0x00)
    for _ in range(7):
        asm.mov("m", "a")
        asm.inx("h")
    asm.mov("m", "a")
    # Select leaf 0 and check vendor byte 0 == 'C'.
    asm.mvi("a", 0x00)
    asm.out(CAPS_INDEX_PORT)
    asm.inp(CAPS_DATA1_PORT)
    asm.cpi(ord("C"))
    asm.jnz("caps_done")
    # caps_present = 1
    asm.lxi("h", CAPSET_BASE)
    asm.mvi("a", 0x01)
    asm.mov("m", "a")
    # Leaf 2: ladder/tier/max (bytes 0..2 of DATA0).
    asm.mvi("a", 0x02)
    asm.out(CAPS_INDEX_PORT)
    asm.lxi("h", CAPSET_BASE + 1)
    asm.inp(CAPS_DATA0_PORT + 0)
    asm.mov("m", "a")
    asm.inx("h")
    asm.inp(CAPS_DATA0_PORT + 1)
    asm.mov("m", "a")
    asm.inx("h")
    asm.inp(CAPS_DATA0_PORT + 2)
    asm.mov("m", "a")
    # Leaf 3: features0 (store MSB..LSB for hex printing).
    asm.mvi("a", 0x03)
    asm.out(CAPS_INDEX_PORT)
    asm.lxi("h", CAPSET_BASE + 4)
    asm.inp(CAPS_DATA0_PORT + 3)
    asm.mov("m", "a")
    asm.inx("h")
    asm.inp(CAPS_DATA0_PORT + 2)
    asm.mov("m", "a")
    asm.inx("h")
    asm.inp(CAPS_DATA0_PORT + 1)
    asm.mov("m", "a")
    asm.inx("h")
    asm.inp(CAPS_DATA0_PORT + 0)
    asm.mov("m", "a")
    asm.label("caps_done")
    asm.ret()


def emit_putc(asm: Asm8080) -> None:
    """Console output: write A to UART data register."""
    asm.label("putc")
    asm.stax("d")
    asm.ret()


def emit_putstr(asm: Asm8080) -> None:
    """Console output: print zero-terminated string at HL."""
    asm.label("putstr")
    asm.mov("a", "m")
    asm.ora("a")
    asm.rz()
    asm.call("putc")
    asm.inx("h")
    asm.jmp("putstr")


def emit_print_hex_nibble(asm: Asm8080) -> None:
    """Print low nibble of A as hex digit."""
    asm.label("print_hex_nibble")
    asm.ani(0x0F)
    asm.adi(ord("0"))
    asm.cpi(ord("9") + 1)
    asm.jc("hex_digit_out")
    asm.adi(7)
    asm.label("hex_digit_out")
    asm.call("putc")
    asm.ret()


def emit_print_hex8(asm: Asm8080) -> None:
    """Print A as two hex digits."""
    asm.label("print_hex8")
    asm.mov("b", "a")
    asm.rrc()
    asm.rrc()
    asm.rrc()
    asm.rrc()
    asm.call("print_hex_nibble")
    asm.mov("a", "b")
    asm.call("print_hex_nibble")
    asm.ret()


def emit_print_hex32(asm: Asm8080) -> None:
    """Print 4 bytes at HL as 8 hex digits (MSB..LSB)."""
    asm.label("print_hex32")
    asm.mvi("c", 0x04)
    asm.label("print_hex32_loop")
    asm.mov("a", "m")
    asm.call("print_hex8")
    asm.inx("h")
    asm.dcr("c")
    asm.jnz("print_hex32_loop")
    asm.ret()


def emit_newline(asm: Asm8080) -> None:
    """Print CRLF."""
    asm.label("newline")
    asm.mvi("a", 0x0D)
    asm.call("putc")
    asm.mvi("a", 0x0A)
    asm.call("putc")
    asm.ret()


def emit_boot_banner(asm: Asm8080) -> None:
    """Print the deterministic boot banner and capability summary."""
    asm.label("boot_banner")
    asm.lxi("h", "msg_banner")
    asm.call("putstr")
    asm.lxi("h", "msg_cpu_prefix")
    asm.call("putstr")
    asm.lda(CAPSET_BASE + 1)
    asm.call("print_hex8")
    asm.lxi("h", "msg_cpu_tier")
    asm.call("putstr")
    asm.lda(CAPSET_BASE + 2)
    asm.call("print_hex8")
    asm.lxi("h", "msg_cpu_max")
    asm.call("putstr")
    asm.lda(CAPSET_BASE + 3)
    asm.call("print_hex8")
    asm.call("newline")
    asm.lxi("h", "msg_caps")
    asm.call("putstr")
    asm.lxi("h", CAPSET_BASE + 4)
    asm.call("print_hex32")
    asm.call("newline")
    asm.ret()


def emit_monitor_stub(asm: Asm8080) -> None:
    """Monitor stub: announce missing monitor and halt."""
    asm.label("monitor_stub")
    asm.lxi("h", "msg_monitor")
    asm.call("putstr")
    asm.hlt()
    asm.jmp("monitor_stub")


def emit_strings(asm: Asm8080) -> None:
    """Emit banner strings."""
    asm.label("msg_banner")
    asm.db("JC-BIOS v0.1\r\n")
    asm.db(0x00)
    asm.label("msg_cpu_prefix")
    asm.db("CPU L=")
    asm.db(0x00)
    asm.label("msg_cpu_tier")
    asm.db(" T=")
    asm.db(0x00)
    asm.label("msg_cpu_max")
    asm.db(" M=")
    asm.db(0x00)
    asm.label("msg_caps")
    asm.db("CAPS0=0x")
    asm.db(0x00)
    asm.label("msg_monitor")
    asm.db("Monitor not yet implemented\r\n")
    asm.db(0x00)


def build_rom_stub() -> bytes:
    """Build the 256-byte ROM stub image."""
    asm = Asm8080(origin=0x0000)
    emit_rom_stub(asm)
    return asm.build(ROM_SIZE)


def build_ram_payload() -> bytes:
    """Build the RAM-resident BIOS payload."""
    asm = Asm8080(origin=BIOS_ENTRY)
    emit_reset(asm)
    emit_caps_probe(asm)
    emit_putc(asm)
    emit_putstr(asm)
    emit_print_hex_nibble(asm)
    emit_print_hex8(asm)
    emit_print_hex32(asm)
    emit_newline(asm)
    emit_boot_banner(asm)
    emit_monitor_stub(asm)
    emit_strings(asm)
    return asm.finish()


def main() -> int:
    parser = argparse.ArgumentParser(description="Build JC-BIOS v0.1 ROM.")
    parser.add_argument(
        "--rom-out",
        default=str(Path(__file__).with_name("jc_bios_v0_1.rom")),
        help="Output ROM stub path.",
    )
    parser.add_argument(
        "--ram-out",
        default=str(Path(__file__).with_name("jc_bios_v0_1_mem.bin")),
        help="Output RAM payload path.",
    )
    args = parser.parse_args()

    rom = build_rom_stub()
    payload = build_ram_payload()

    rom_path = Path(args.rom_out)
    rom_path.parent.mkdir(parents=True, exist_ok=True)
    rom_path.write_bytes(rom)

    ram_path = Path(args.ram_out)
    ram_path.parent.mkdir(parents=True, exist_ok=True)
    ram_path.write_bytes(payload)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
