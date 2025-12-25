CC ?= gcc
CFLAGS ?= -std=c89 -Wall -Wextra -Werror
CPPFLAGS ?= -Isource/common/include -Isource/common/util -Isource/firmware/JC-BIOS/include -Isource/os/JC-DOS/include

EXEEXT :=
ifeq ($(OS),Windows_NT)
  EXEEXT := .exe
endif

GENSPEC := source/tools/host/genspec/genspec$(EXEEXT)
GENSPEC_SRC := source/tools/host/genspec/genspec.c
GENSPEC_DEFS := source/common/spec/defs/defs.lst
GENSPEC_DEF_FILES := \
	source/common/spec/defs/spec_tiers.def \
	source/common/spec/defs/spec_profiles.def \
	source/common/spec/defs/spec_mode.def \
	source/common/spec/defs/spec_discovery.def \
	source/common/spec/defs/spec_capset.def \
	source/common/spec/defs/spec_topology.def \
	source/common/spec/defs/spec_bdt.def \
	source/common/spec/defs/spec_irq.def \
	source/common/spec/defs/spec_dev_uart.def \
	source/common/spec/defs/spec_dev_timer.def \
	source/common/spec/defs/spec_dev_pic.def \
	source/common/spec/defs/spec_dev_storage_idepio.def \
	source/common/spec/defs/spec_cai.def \
	source/common/spec/defs/spec_jcom.def \
	source/common/spec/defs/spec_fs_cpmx.def \
	source/common/spec/defs/spec_conformance.def

AUTOGEN_HEADERS := \
	source/common/include/jc_contracts_autogen.h \
	source/common/include/jc_offsets_autogen.h

MKDISK := source/tools/host/mkdisk/mkdisk$(EXEEXT)
MKJCOM := source/tools/host/mkjcom/mkjcom$(EXEEXT)
TRANSCRIPT_CMP := source/tools/host/transcript_cmp/transcript_cmp$(EXEEXT)
HOST_TOOLS := $(GENSPEC) $(MKDISK) $(MKJCOM) $(TRANSCRIPT_CMP)

BIOS_CORE_SRCS := \
	source/firmware/JC-BIOS/core/boot.c \
	source/firmware/JC-BIOS/core/bdt.c \
	source/firmware/JC-BIOS/core/capset.c \
	source/firmware/JC-BIOS/core/console.c \
	source/firmware/JC-BIOS/core/conformance.c \
	source/firmware/JC-BIOS/core/discovery.c \
	source/firmware/JC-BIOS/core/fs_cpmx.c \
	source/firmware/JC-BIOS/core/loader_jcom.c \
	source/firmware/JC-BIOS/core/mode.c \
	source/firmware/JC-BIOS/core/monitor.c \
	source/firmware/JC-BIOS/core/timer.c \
	source/firmware/JC-BIOS/core/util.c \
	source/common/util/jc_arena.c

BIOS_DRIVER_SRCS := \
	source/firmware/JC-BIOS/drivers/carbonkio_uart.c \
	source/firmware/JC-BIOS/drivers/carbonkio_timer.c \
	source/firmware/JC-BIOS/drivers/carbonkio_pic.c \
	source/firmware/JC-BIOS/drivers/carbonstorage_idepio.c

BIOS_CORE_OBJS := $(BIOS_CORE_SRCS:.c=.o)
BIOS_DRIVER_OBJS := $(BIOS_DRIVER_SRCS:.c=.o)
BIOS_BSP_OBJS := \
	source/firmware/JC-BIOS/bsp/sim_ref/bsp_sim_ref.o \
	source/firmware/JC-BIOS/bsp/fpga_ref/bsp_fpga_ref.o \
	source/firmware/JC-BIOS/bsp/hw_ref1/bsp_hw_ref1.o

DOS_SRCS := source/os/JC-DOS/kernel/jc_dos_stub.c
DOS_OBJS := $(DOS_SRCS:.c=.o)

.PHONY: all bios dos clean sim_ref_rom conformance_v0_1 conformance_v0_2 conformance_v0_3 \
	conformance_v0_4 conformance_v0_5 conformance_v0_6

all: $(HOST_TOOLS) $(AUTOGEN_HEADERS) bios dos

$(GENSPEC): $(GENSPEC_SRC)
	$(CC) $(CFLAGS) -o $@ $<

$(MKDISK): source/tools/host/mkdisk/mkdisk.c $(AUTOGEN_HEADERS)
	$(CC) $(CFLAGS) $(CPPFLAGS) -o $@ $<

$(MKJCOM): source/tools/host/mkjcom/mkjcom.c $(AUTOGEN_HEADERS)
	$(CC) $(CFLAGS) $(CPPFLAGS) -o $@ $<

$(TRANSCRIPT_CMP): source/tools/host/transcript_cmp/transcript_cmp.c
	$(CC) $(CFLAGS) $(CPPFLAGS) -o $@ $<

$(AUTOGEN_HEADERS): $(GENSPEC) $(GENSPEC_DEFS) $(GENSPEC_DEF_FILES)
	$(GENSPEC) --list $(GENSPEC_DEFS) --out-dir source/common/include

bios: $(BIOS_CORE_OBJS) $(BIOS_DRIVER_OBJS) $(BIOS_BSP_OBJS)

dos: $(DOS_OBJS)

%.o: %.c $(AUTOGEN_HEADERS)
	$(CC) $(CFLAGS) $(CPPFLAGS) -c $< -o $@

clean:
	rm -f $(HOST_TOOLS) $(BIOS_CORE_OBJS) $(BIOS_DRIVER_OBJS) \
		$(BIOS_BSP_OBJS) $(DOS_OBJS) $(AUTOGEN_HEADERS)

# SIM_REF ROM build (requires external Z80 toolchain)
Z80_CC ?= sdcc
Z80_AS ?= sdasz80
Z80_LD ?= sdldz80

SIM_REF_ROM ?= source/firmware/JC-BIOS/bsp/sim_ref/jc_bios_sim_ref.rom
SIM_REF_DEFS ?=

sim_ref_rom: $(GENSPEC) $(AUTOGEN_HEADERS)
	@echo Building SIM_REF ROM with $(Z80_CC)
	@echo NOTE: configure Z80_CC/Z80_AS/Z80_LD if needed.
	@$(Z80_CC) --version > NUL 2>&1
	@$(Z80_CC) -c -mz80 --std-c89 $(SIM_REF_DEFS) -I./source/common/include \
		-I./source/common/util \
		-I./source/firmware/JC-BIOS/include \
		$(BIOS_CORE_SRCS) $(BIOS_DRIVER_SRCS) \
		source/firmware/JC-BIOS/bsp/sim_ref/bsp_sim_ref.c
	@$(Z80_AS) -o source/firmware/JC-BIOS/arch/z80/reset.rel \
		source/firmware/JC-BIOS/arch/z80/reset.S
	@$(Z80_AS) -o source/firmware/JC-BIOS/arch/z80/mode_tramp.rel \
		source/firmware/JC-BIOS/arch/z80/mode_tramp.S
	@$(Z80_LD) -i $(SIM_REF_ROM) *.rel source/firmware/JC-BIOS/arch/z80/*.rel
	@echo Wrote $(SIM_REF_ROM)

conformance_v0_1:
	@$(MAKE) sim_ref_rom SIM_REF_ROM=source/firmware/JC-BIOS/bsp/sim_ref/jc_bios_sim_ref_v0_1.rom \
		SIM_REF_DEFS=-DJC_CONFORMANCE_V0_1
	@echo Run SIM_REF with jc_bios_sim_ref_v0_1.rom and capture transcript.

conformance_v0_2:
	@$(MAKE) sim_ref_rom SIM_REF_ROM=source/firmware/JC-BIOS/bsp/sim_ref/jc_bios_sim_ref_v0_2.rom \
		SIM_REF_DEFS=-DJC_CONFORMANCE_V0_2
	@echo Run SIM_REF with jc_bios_sim_ref_v0_2.rom and capture transcript.

conformance_v0_3:
	@$(MAKE) sim_ref_rom SIM_REF_ROM=source/firmware/JC-BIOS/bsp/sim_ref/jc_bios_sim_ref_v0_3.rom \
		SIM_REF_DEFS=-DJC_CONFORMANCE_V0_3
	@echo Run SIM_REF with jc_bios_sim_ref_v0_3.rom and capture transcript.

conformance_v0_4:
	@$(MAKE) sim_ref_rom SIM_REF_ROM=source/firmware/JC-BIOS/bsp/sim_ref/jc_bios_sim_ref_v0_4.rom \
		SIM_REF_DEFS=-DJC_CONFORMANCE_V0_4
	@echo Run SIM_REF with jc_bios_sim_ref_v0_4.rom and capture transcript.

conformance_v0_5:
	@$(MAKE) sim_ref_rom SIM_REF_ROM=source/firmware/JC-BIOS/bsp/sim_ref/jc_bios_sim_ref_v0_5.rom \
		SIM_REF_DEFS=-DJC_CONFORMANCE_V0_5
	@echo Run SIM_REF with jc_bios_sim_ref_v0_5.rom and capture transcript.

conformance_v0_6:
	@$(MAKE) sim_ref_rom SIM_REF_ROM=source/firmware/JC-BIOS/bsp/sim_ref/jc_bios_sim_ref_v0_6.rom \
		SIM_REF_DEFS=-DJC_CONFORMANCE_V0_6
	@echo Run SIM_REF with jc_bios_sim_ref_v0_6.rom and capture transcript.
