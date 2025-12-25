CC ?= gcc
CFLAGS ?= -std=c89 -Wall -Wextra -Werror
CPPFLAGS ?= -Isource/common/include -Isource/common/util -Isource/firmware/JC-BIOS/include \
	-Isource/os/JC-DOS/include -Isource/os/JC-DOS/kernel -Isource/os/JC-DOS/drivers \
	-Isource/os/JC-DOS/fs -Isource/os/JC-DOS/shell

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
	source/firmware/JC-BIOS/core/bios_services.c \
	source/firmware/JC-BIOS/core/boot.c \
	source/firmware/JC-BIOS/core/block_robust.c \
	source/firmware/JC-BIOS/core/bdt.c \
	source/firmware/JC-BIOS/core/capset.c \
	source/firmware/JC-BIOS/core/console.c \
	source/firmware/JC-BIOS/core/conformance.c \
	source/firmware/JC-BIOS/core/discovery.c \
	source/firmware/JC-BIOS/core/fs_cpmx.c \
	source/firmware/JC-BIOS/core/irq.c \
	source/firmware/JC-BIOS/core/loader_jcom.c \
	source/firmware/JC-BIOS/core/mode.c \
	source/firmware/JC-BIOS/core/monitor.c \
	source/firmware/JC-BIOS/core/timer.c \
	source/firmware/JC-BIOS/core/util.c \
	source/common/util/jc_arena.c \
	source/common/util/jc_dma.c \
	source/common/util/jc_ringbuf.c

BIOS_STORAGE_DRIVER ?= idepio
ifeq ($(BIOS_STORAGE_DRIVER),idepio)
  BIOS_STORAGE_DRIVER_SRC := source/firmware/JC-BIOS/drivers/carbonstorage_idepio.c
else ifeq ($(BIOS_STORAGE_DRIVER),ide_alt1)
  BIOS_STORAGE_DRIVER_SRC := source/firmware/JC-BIOS/drivers/carbonstorage_ide_alt1.c
else ifeq ($(BIOS_STORAGE_DRIVER),dma)
  BIOS_STORAGE_DRIVER_SRC := source/firmware/JC-BIOS/drivers/carbonstorage_dma.c
else
  BIOS_STORAGE_DRIVER_SRC := source/firmware/JC-BIOS/drivers/carbonstorage_idepio.c
endif

BIOS_DRIVER_SRCS := \
	source/firmware/JC-BIOS/drivers/carbonkio_uart.c \
	source/firmware/JC-BIOS/drivers/carbonkio_timer.c \
	source/firmware/JC-BIOS/drivers/carbonkio_pic.c \
	$(BIOS_STORAGE_DRIVER_SRC)

BIOS_CORE_OBJS := $(BIOS_CORE_SRCS:.c=.o)
BIOS_DRIVER_OBJS := $(BIOS_DRIVER_SRCS:.c=.o)
BIOS_BSP_OBJS := \
	source/firmware/JC-BIOS/bsp/sim_ref/bsp_sim_ref.o \
	source/firmware/JC-BIOS/bsp/fpga_ref/bsp_fpga_ref.o \
	source/firmware/JC-BIOS/bsp/hw_ref1/bsp_hw_ref1.o

DOS_SRCS := \
	source/common/util/jc_component.c \
	source/common/util/jc_fastmem.c \
	source/common/util/jc_profile.c \
	source/common/util/jc_cai.c \
	source/common/util/jc_fpu.c \
	source/common/util/jc_fpu_soft.c \
	source/common/util/jc_fpu_am9513_cai.c \
	source/common/util/jc_fpu_am9511_win.c \
	source/common/util/jc_fpu_am9512_win.c \
	source/common/util/jc_display.c \
	source/os/JC-DOS/kernel/dos_conformance.c \
	source/os/JC-DOS/kernel/dos_entry.c \
	source/os/JC-DOS/kernel/dos_util.c \
	source/os/JC-DOS/kernel/exec_jcom.c \
	source/os/JC-DOS/kernel/log.c \
	source/os/JC-DOS/kernel/cache_blk.c \
	source/os/JC-DOS/kernel/cai_init.c \
	source/os/JC-DOS/kernel/component_list.c \
	source/os/JC-DOS/kernel/display_init.c \
	source/os/JC-DOS/kernel/mem_arena.c \
	source/os/JC-DOS/kernel/personality.c \
	source/os/JC-DOS/kernel/panic.c \
	source/os/JC-DOS/drivers/bios_services.c \
	source/os/JC-DOS/drivers/video_common.c \
	source/os/JC-DOS/drivers/video_mc6845.c \
	source/os/JC-DOS/drivers/video_mda.c \
	source/os/JC-DOS/drivers/video_cga_ega_vga.c \
	source/os/JC-DOS/drivers/video_tms9918.c \
	source/os/JC-DOS/drivers/video_v99x8.c \
	source/os/JC-DOS/fs/fs_cpmx.c \
	source/os/JC-DOS/fs/fs_romfs.c \
	source/os/JC-DOS/shell/parse.c \
	source/os/JC-DOS/shell/shell.c \
	source/os/JC-DOS/shell/shell_cmds.c
DOS_OBJS := $(DOS_SRCS:.c=.o)

.PHONY: all bios dos clean sim_ref_rom conformance_v0_1 conformance_v0_2 conformance_v0_3 \
	conformance_v0_4 conformance_v0_5 conformance_v0_6 conformance_v1_7 dos_ihx dos_bin dos_jcom \
	dos_disk sim_ref_dos dos_conformance_v0_7 dos_conformance_v0_8 dos_conformance_v0_9 \
	dos_conformance_v1_0 dos_conformance_v1_1 dos_conformance_v1_2 \
	dos_conformance_v1_3 dos_conformance_v1_4 dos_conformance_v1_8 \
	dos_conformance_v1_8_irq \
	dos_conformance_v2_0

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
		$(BIOS_BSP_OBJS) $(DOS_OBJS) $(AUTOGEN_HEADERS) \
		$(DOS_IHX) $(DOS_BIN) $(DOS_JCOM) $(DOS_DISK)

# SIM_REF ROM build (requires external Z80 toolchain)
Z80_CC ?= sdcc
Z80_AS ?= sdasz80
Z80_LD ?= sdldz80

SIM_REF_ROM ?= source/firmware/JC-BIOS/bsp/sim_ref/jc_bios_sim_ref.rom
SIM_REF_DEFS ?=

# JC-DOS JCOM build (requires external Z80 toolchain)
DOS_CC ?= $(Z80_CC)
DOS_MAKEBIN ?= makebin
DOS_LOAD_ADDR ?= 0x8000
DOS_ENTRY_OFFSET ?= 0
DOS_BSS_SIZE ?= 0
DOS_MIN_TIER ?= 0
DOS_BOOT_NAME ?= JCDOS.JCO
DOS_IHX ?= build/jcdos.ihx
DOS_BIN ?= build/jcdos.bin
DOS_JCOM ?= build/$(DOS_BOOT_NAME)
DOS_DISK ?= build/jcdos.img
DOS_DISK_SECTORS ?= 2048
DOS_DIR_ENTRIES ?= 128
DOS_SECTORS_PER_BLOCK ?= 1
DOS_VOLUME_ID ?= 0x4A43444Fu
DOS_DEFS ?=

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

dos_ihx: $(GENSPEC) $(AUTOGEN_HEADERS)
	@echo Building JC-DOS IHX with $(DOS_CC)
	@echo NOTE: DOS_ENTRY_OFFSET defaults to 0; adjust if linker places entry elsewhere.
	@$(DOS_CC) --version > NUL 2>&1
	@$(DOS_CC) -mz80 --std-c89 --code-loc $(DOS_LOAD_ADDR) --data-loc $(DOS_LOAD_ADDR) \
		$(DOS_DEFS) -I./source/common/include -I./source/common/util \
		-I./source/os/JC-DOS/include -I./source/os/JC-DOS/kernel \
		-I./source/os/JC-DOS/drivers -I./source/os/JC-DOS/fs \
		-I./source/os/JC-DOS/shell \
		-o $(DOS_IHX) $(DOS_SRCS)

dos_bin: dos_ihx
	@$(DOS_MAKEBIN) -p $(DOS_IHX) $(DOS_BIN)
	@echo Wrote $(DOS_BIN)

dos_jcom: $(MKJCOM) dos_bin
	@$(MKJCOM) $(DOS_BIN) $(DOS_JCOM) $(DOS_LOAD_ADDR) $(DOS_ENTRY_OFFSET) \
		$(DOS_BSS_SIZE) $(DOS_MIN_TIER)
	@echo Wrote $(DOS_JCOM)

dos_disk: $(MKDISK) dos_jcom
	@$(MKDISK) $(DOS_DISK) $(DOS_DISK_SECTORS) $(DOS_DIR_ENTRIES) \
		$(DOS_SECTORS_PER_BLOCK) $(DOS_VOLUME_ID) \
		$(DOS_BOOT_NAME)=$(DOS_JCOM)
	@echo Wrote $(DOS_DISK)

sim_ref_dos: sim_ref_rom dos_disk
	@echo Run SIM_REF with:
	@echo "  carbon-sim --platform carbonz80 --rom $(SIM_REF_ROM) --disk0 $(DOS_DISK)"
	@echo "Capture output and compare with transcript_cmp as needed."

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

conformance_v1_7:
	@$(MAKE) sim_ref_rom SIM_REF_ROM=source/firmware/JC-BIOS/bsp/sim_ref/jc_bios_sim_ref_v1_7.rom \
		SIM_REF_DEFS=-DJC_CONFORMANCE_V1_7
	@echo Run SIM_REF with jc_bios_sim_ref_v1_7.rom and capture transcript.

dos_conformance_v0_7:
	@$(MAKE) dos_disk DOS_DEFS=-DJC_DOS_CONFORMANCE_V0_7 \
		DOS_JCOM=build/JCDOS_V0_7.JCO DOS_DISK=build/jcdos_v0_7.img
	@echo Run SIM_REF with jc_bios_sim_ref.rom and build/jcdos_v0_7.img and capture transcript.

dos_conformance_v0_8:
	@$(MAKE) dos_disk DOS_DEFS=-DJC_DOS_CONFORMANCE_V0_8 \
		DOS_JCOM=build/JCDOS_V0_8.JCO DOS_DISK=build/jcdos_v0_8.img
	@echo Run SIM_REF with jc_bios_sim_ref.rom and build/jcdos_v0_8.img and capture transcript.

dos_conformance_v0_9:
	@$(MAKE) dos_disk DOS_DEFS=-DJC_DOS_CONFORMANCE_V0_9 \
		DOS_JCOM=build/JCDOS_V0_9.JCO DOS_DISK=build/jcdos_v0_9.img
	@echo Run SIM_REF with jc_bios_sim_ref.rom and build/jcdos_v0_9.img and capture transcript.

dos_conformance_v1_0:
	@$(MAKE) dos_disk DOS_DEFS=-DJC_DOS_CONFORMANCE_V1_0 \
		DOS_JCOM=build/JCDOS_V1_0.JCO DOS_DISK=build/jcdos_v1_0.img
	@echo Run SIM_REF with jc_bios_sim_ref.rom and build/jcdos_v1_0.img and capture transcript.

dos_conformance_v1_1:
	@$(MAKE) dos_disk DOS_DEFS="-DJC_DOS_CONFORMANCE_V1_1 -DJC_CFG_ENABLE_CACHE=1 \
		-DJC_CFG_ENABLE_FASTMEM=1 -DJC_CFG_FASTMEM_CAPS=1u" \
		DOS_JCOM=build/JCDOS_V1_1.JCO DOS_DISK=build/jcdos_v1_1.img
	@echo Run SIM_REF with jc_bios_sim_ref.rom and build/jcdos_v1_1.img and capture transcript.

dos_conformance_v1_2:
	@$(MAKE) sim_ref_rom SIM_REF_DEFS=-DJC_SIM_ENABLE_CAI \
		SIM_REF_ROM=source/firmware/JC-BIOS/bsp/sim_ref/jc_bios_sim_ref_v1_2.rom
	@$(MAKE) dos_disk DOS_DEFS="-DJC_DOS_CONFORMANCE_V1_2 -DJC_CFG_ENABLE_CAI=1 \
		-DJC_CFG_ENABLE_FPU=1" \
		DOS_JCOM=build/JCDOS_V1_2.JCO DOS_DISK=build/jcdos_v1_2.img
	@echo Run SIM_REF with jc_bios_sim_ref_v1_2.rom and build/jcdos_v1_2.img and capture transcript.

dos_conformance_v1_3:
	@$(MAKE) dos_disk DOS_DEFS="-DJC_DOS_CONFORMANCE_V1_3 \
		-DJC_CFG_ENABLE_DISPLAY_BACKENDS=1 -DJC_CFG_ENABLE_DISPLAY_SHADOW=1" \
		DOS_JCOM=build/JCDOS_V1_3.JCO DOS_DISK=build/jcdos_v1_3.img
	@echo Run SIM_REF with jc_bios_sim_ref.rom and build/jcdos_v1_3.img and capture transcript.

dos_conformance_v1_4:
	@$(MAKE) dos_disk DOS_DEFS=-DJC_DOS_CONFORMANCE_V1_4 \
		DOS_JCOM=build/JCDOS_V1_4.JCO DOS_DISK=build/jcdos_v1_4.img
	@echo Run SIM_REF with jc_bios_sim_ref.rom and build/jcdos_v1_4.img and capture transcript.

dos_conformance_v1_8:
	@$(MAKE) dos_disk DOS_DEFS=-DJC_DOS_CONFORMANCE_V1_8 \
		DOS_JCOM=build/JCDOS_V1_8.JCO DOS_DISK=build/jcdos_v1_8.img
	@echo Run SIM_REF with jc_bios_sim_ref.rom and build/jcdos_v1_8.img (polling) and capture transcript.

dos_conformance_v1_8_irq:
	@$(MAKE) sim_ref_rom SIM_REF_ROM=source/firmware/JC-BIOS/bsp/sim_ref/jc_bios_sim_ref_v1_8_irq.rom \
		SIM_REF_DEFS="-DJC_CFG_ENABLE_IRQ=1 -DJC_SIM_ENABLE_IRQ -DJC_SIM_IRQ_INJECT_SPURIOUS"
	@$(MAKE) dos_disk DOS_DEFS=-DJC_DOS_CONFORMANCE_V1_8 \
		DOS_JCOM=build/JCDOS_V1_8_IRQ.JCO DOS_DISK=build/jcdos_v1_8_irq.img
	@echo Run SIM_REF with jc_bios_sim_ref_v1_8_irq.rom and build/jcdos_v1_8_irq.img (IRQ mode) and capture transcript.

dos_conformance_v2_0:
	@$(MAKE) sim_ref_rom SIM_REF_ROM=source/firmware/JC-BIOS/bsp/sim_ref/jc_bios_sim_ref_v2_0.rom \
		SIM_REF_DEFS="-DJC_BSP_PROFILE_ID=JC_PROFILE_MCU"
	@$(MAKE) dos_disk DOS_DEFS="-DJC_DOS_CONFORMANCE_V2_0 -DJC_CFG_SHELL_MINIMAL=1 \
		-DJC_CFG_ENABLE_CACHE=0 -DJC_CFG_ENABLE_CPM_COMPAT=0" \
		DOS_JCOM=build/JCDOS_V2_0.JCO DOS_DISK=build/jcdos_v2_0.img
	@echo Run SIM_REF with jc_bios_sim_ref_v2_0.rom and build/jcdos_v2_0.img (PROFILE_MCU) and capture transcript.
