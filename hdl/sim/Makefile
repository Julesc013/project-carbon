# Project Carbon - Simulation runner (structure only)
#
# Intended usage (requires a simulator):
#   make tb_fabric_arbiter
#   make tb_irq_ctrl
#   make tb_ipi_mailbox
#   make tb_trace_ring
#   make tb_cai_contract
#   make tb_z85
#   make tb_z90
#   make tb_am9513
#   make tb_ez90_scaffold
#   make tb_8096
#   make tb_8097
#   make tb_carbonz80
#   make tb_carbonz90
#   make tb_carbonez90
#   make tb_carbonx86
#   make tb_carbonx96
#
# Uses Icarus Verilog if available.

IVERILOG ?= iverilog
VVP      ?= vvp

BUILD_DIR := build

COMMON_SV := \
  ../gen/carbon_arch_pkg.sv \
  ../common/if/*.sv \
  ../common/fabric/*.sv \
  ../common/irq/*.sv \
  ../common/ipc/*.sv \
  ../common/debug/*.sv \
  ../common/capability/*.sv \
  bfm/*.sv

CARBONIO_SV := \
  ../cores/CarbonIO/rtl/carbonio_pkg.sv \
  ../cores/CarbonIO/rtl/carbonio_fifo.sv \
  ../cores/CarbonIO/rtl/carbonio_uart.sv \
  ../cores/CarbonIO/rtl/carbonio_pio.sv \
  ../cores/CarbonIO/rtl/carbonio_timer.sv \
  ../cores/CarbonIO/rtl/carbonio_irq_router.sv \
  ../cores/CarbonIO/rtl/carbonio.sv \
  ../cores/CarbonIO/tb/tb_carbonio.sv

AM9513_SV := \
  ../cores/Am9513/rtl/am9513_pkg.sv \
  ../cores/Am9513/rtl/am9513_math_pkg.sv \
  ../cores/Am9513/rtl/am9513_context_file.sv \
  ../cores/Am9513/rtl/am9513_legacy_shell.sv \
  ../cores/Am9513/rtl/am9513_cai_engine.sv \
  ../cores/Am9513/rtl/am9513_accel.sv \
  ../cores/Am9513/tb/tb_am9513.sv

AM9513_RTL_SV := \
  ../cores/Am9513/rtl/am9513_pkg.sv \
  ../cores/Am9513/rtl/am9513_math_pkg.sv \
  ../cores/Am9513/rtl/am9513_context_file.sv \
  ../cores/Am9513/rtl/am9513_legacy_shell.sv \
  ../cores/Am9513/rtl/am9513_cai_engine.sv \
  ../cores/Am9513/rtl/am9513_accel.sv

EZ90_SV := \
  ../cores/eZ90/rtl/ez90_pkg.sv \
  ../cores/eZ90/rtl/uop_queue.sv \
  ../cores/eZ90/rtl/fe_bpred.sv \
  ../cores/eZ90/rtl/fe_icache_port.sv \
  ../cores/eZ90/rtl/fe_fetch.sv \
  ../cores/eZ90/rtl/fe_decode.sv \
  ../cores/eZ90/rtl/fe_uop_cache.sv \
  ../cores/eZ90/rtl/renamer.sv \
  ../cores/eZ90/rtl/dispatch.sv \
  ../cores/eZ90/rtl/rob.sv \
  ../cores/eZ90/rtl/rs_int.sv \
  ../cores/eZ90/rtl/lsq.sv \
  ../cores/eZ90/rtl/scheduler.sv \
  ../cores/eZ90/rtl/exec_int_alu.sv \
  ../cores/eZ90/rtl/exec_branch.sv \
  ../cores/eZ90/rtl/exec_muldiv.sv \
  ../cores/eZ90/rtl/exec_vec.sv \
  ../cores/eZ90/rtl/writeback.sv \
  ../cores/eZ90/rtl/commit.sv \
  ../cores/eZ90/rtl/priv_ctrl.sv \
  ../cores/eZ90/rtl/mmu.sv \
  ../cores/eZ90/rtl/trap_unit.sv \
  ../cores/eZ90/rtl/iommu_hook.sv \
  ../cores/eZ90/rtl/icache_port.sv \
  ../cores/eZ90/rtl/dcache_port.sv \
  ../cores/eZ90/rtl/cpuid_block.sv \
  ../cores/eZ90/rtl/ez90_core.sv \
  ../cores/eZ90/tb/tb_ez90_scaffold.sv

EZ90_RTL_SV := \
  ../cores/eZ90/rtl/ez90_pkg.sv \
  ../cores/eZ90/rtl/uop_queue.sv \
  ../cores/eZ90/rtl/fe_bpred.sv \
  ../cores/eZ90/rtl/fe_icache_port.sv \
  ../cores/eZ90/rtl/fe_fetch.sv \
  ../cores/eZ90/rtl/fe_decode.sv \
  ../cores/eZ90/rtl/fe_uop_cache.sv \
  ../cores/eZ90/rtl/renamer.sv \
  ../cores/eZ90/rtl/dispatch.sv \
  ../cores/eZ90/rtl/rob.sv \
  ../cores/eZ90/rtl/rs_int.sv \
  ../cores/eZ90/rtl/lsq.sv \
  ../cores/eZ90/rtl/scheduler.sv \
  ../cores/eZ90/rtl/exec_int_alu.sv \
  ../cores/eZ90/rtl/exec_branch.sv \
  ../cores/eZ90/rtl/exec_muldiv.sv \
  ../cores/eZ90/rtl/exec_vec.sv \
  ../cores/eZ90/rtl/writeback.sv \
  ../cores/eZ90/rtl/commit.sv \
  ../cores/eZ90/rtl/priv_ctrl.sv \
  ../cores/eZ90/rtl/mmu.sv \
  ../cores/eZ90/rtl/trap_unit.sv \
  ../cores/eZ90/rtl/iommu_hook.sv \
  ../cores/eZ90/rtl/icache_port.sv \
  ../cores/eZ90/rtl/dcache_port.sv \
  ../cores/eZ90/rtl/cpuid_block.sv \
  ../cores/eZ90/rtl/ez90_core.sv

Z85_RTL_SV := \
  ../cores/Z85/rtl/z85_regfile.sv \
  ../cores/Z85/rtl/z85_flags.sv \
  ../cores/Z85/rtl/z85_decode.sv \
  ../cores/Z85/rtl/z85_core.sv

Z85_SV := \
  $(Z85_RTL_SV) \
  ../cores/Z85/ref/z85_ref_model.sv \
  ../cores/Z85/tb/tb_z85.sv

Z90_RTL_SV := \
  $(Z85_RTL_SV) \
  ../cores/Z90/rtl/z90_decode_pkg.sv \
  ../cores/Z90/rtl/z90_alu_pkg.sv \
  ../cores/Z90/rtl/z90_core.sv

Z90_SV := \
  $(Z90_RTL_SV) \
  ../cores/Z90/tb/tb_z90.sv

X96_8096_RTL_SV := \
  ../cores/8096/rtl/cpu_8096_pkg.sv \
  ../cores/8096/rtl/cpu_8096_core.sv \
  ../cores/8096/rtl/cpu_8096.sv

X96_8097_RTL_SV := \
  ../cores/Am9513/rtl/am9513_math_pkg.sv \
  ../cores/8097/rtl/fpu_8097_pkg.sv \
  ../cores/8097/rtl/fpu_8097.sv

SYSTEMS_COMMON_SV := \
  ../systems/common/rtl/carbon_memmap_pkg.sv \
  ../systems/common/rtl/carbon_bootrom.sv \
  ../systems/common/rtl/carbon_sram.sv \
  ../systems/common/rtl/carbon_mmio_regs.sv \
  ../systems/common/rtl/carbon_cai_router.sv \
  ../systems/common/rtl/carbon_csr_master_simple.sv \
  ../systems/common/rtl/carbon_fabric_bootmaster.sv \
  ../systems/common/rtl/z80_bus_adapter_stub.sv \
  ../systems/common/rtl/x86_bus_adapter_stub.sv \
  ../systems/common/rtl/csr_master_tieoff.sv \
  ../systems/common/rtl/dbg_hub_tieoff.sv \
  ../systems/common/rtl/irq_src_tieoff.sv \
  ../systems/common/rtl/cai_host_tieoff.sv

CARBONZ80_SV := \
  $(SYSTEMS_COMMON_SV) \
  $(Z85_RTL_SV) \
  $(AM9513_RTL_SV) \
  ../systems/CarbonZ80/rtl/carbonz80_top.sv \
  ../systems/CarbonZ80/tb/tb_carbonz80.sv

CARBONZ90_SV := \
  $(SYSTEMS_COMMON_SV) \
  $(Z90_RTL_SV) \
  $(AM9513_RTL_SV) \
  ../systems/CarbonZ90/rtl/carbonz90_top.sv \
  ../systems/CarbonZ90/tb/tb_carbonz90.sv

CARBONEZ90_SV := \
  $(SYSTEMS_COMMON_SV) \
  $(EZ90_RTL_SV) \
  $(AM9513_RTL_SV) \
  ../systems/CarbonEZ90/rtl/carbonez90_top.sv \
  ../systems/CarbonEZ90/tb/tb_carbonez90.sv

CARBONX86_SV := \
  $(SYSTEMS_COMMON_SV) \
  $(X96_8096_RTL_SV) \
  $(X96_8097_RTL_SV) \
  ../systems/CarbonX86/rtl/carbonx86_top.sv \
  ../systems/CarbonX86/tb/tb_carbonx86.sv

CARBONX96_SV := \
  $(SYSTEMS_COMMON_SV) \
  $(X96_8096_RTL_SV) \
  $(X96_8097_RTL_SV) \
  ../systems/CarbonX96/rtl/carbonx96_top.sv \
  ../systems/CarbonX96/tb/tb_carbonx96.sv

X96_8096_SV := \
  ../cores/8096/rtl/cpu_8096_pkg.sv \
  ../cores/8096/rtl/cpu_8096_core.sv \
  ../cores/8096/rtl/cpu_8096.sv \
  ../cores/8096/tb/tb_8096.sv

X96_8097_SV := \
  ../cores/Am9513/rtl/am9513_pkg.sv \
  ../cores/Am9513/rtl/am9513_math_pkg.sv \
  ../cores/8097/rtl/fpu_8097_pkg.sv \
  ../cores/8097/rtl/fpu_8097.sv \
  ../cores/8097/tb/tb_8097.sv

IVERILOG_FLAGS := -g2012 -Wall -Wno-timescale

.PHONY: all clean tb_fabric_arbiter tb_irq_ctrl tb_ipi_mailbox tb_trace_ring tb_cai_contract tb_z85 tb_z90 tb_am9513 tb_carbonio tb_ez90_scaffold tb_8096 tb_8097 tb_carbonz80 tb_carbonz90 tb_carbonez90 tb_carbonx86 tb_carbonx96
all: tb_fabric_arbiter tb_irq_ctrl tb_ipi_mailbox tb_trace_ring tb_cai_contract tb_z85 tb_z90 tb_am9513 tb_ez90_scaffold tb_8096 tb_8097 tb_carbonz80 tb_carbonz90 tb_carbonez90 tb_carbonx86 tb_carbonx96

$(BUILD_DIR):
	mkdir -p $(BUILD_DIR)

tb_fabric_arbiter: $(BUILD_DIR)
	$(IVERILOG) $(IVERILOG_FLAGS) -o $(BUILD_DIR)/tb_fabric_arbiter.vvp $(COMMON_SV) tb/tb_fabric_arbiter.sv
	$(VVP) $(BUILD_DIR)/tb_fabric_arbiter.vvp

tb_irq_ctrl: $(BUILD_DIR)
	$(IVERILOG) $(IVERILOG_FLAGS) -o $(BUILD_DIR)/tb_irq_ctrl.vvp $(COMMON_SV) tb/tb_irq_ctrl.sv
	$(VVP) $(BUILD_DIR)/tb_irq_ctrl.vvp

tb_ipi_mailbox: $(BUILD_DIR)
	$(IVERILOG) $(IVERILOG_FLAGS) -o $(BUILD_DIR)/tb_ipi_mailbox.vvp $(COMMON_SV) tb/tb_ipi_mailbox.sv
	$(VVP) $(BUILD_DIR)/tb_ipi_mailbox.vvp

tb_trace_ring: $(BUILD_DIR)
	$(IVERILOG) $(IVERILOG_FLAGS) -o $(BUILD_DIR)/tb_trace_ring.vvp $(COMMON_SV) tb/tb_trace_ring.sv
	$(VVP) $(BUILD_DIR)/tb_trace_ring.vvp

tb_cai_contract: $(BUILD_DIR)
	$(IVERILOG) $(IVERILOG_FLAGS) -o $(BUILD_DIR)/tb_cai_contract.vvp $(COMMON_SV) $(AM9513_RTL_SV) tb/tb_cai_contract.sv
	$(VVP) $(BUILD_DIR)/tb_cai_contract.vvp

tb_z85: $(BUILD_DIR)
	$(IVERILOG) $(IVERILOG_FLAGS) -o $(BUILD_DIR)/tb_z85.vvp $(COMMON_SV) $(Z85_SV)
	$(VVP) $(BUILD_DIR)/tb_z85.vvp

tb_z90: $(BUILD_DIR)
	$(IVERILOG) $(IVERILOG_FLAGS) -o $(BUILD_DIR)/tb_z90.vvp $(COMMON_SV) $(Z90_SV)
	$(VVP) $(BUILD_DIR)/tb_z90.vvp

tb_am9513: $(BUILD_DIR)
	$(IVERILOG) $(IVERILOG_FLAGS) -o $(BUILD_DIR)/tb_am9513.vvp $(COMMON_SV) $(AM9513_SV)
	$(VVP) $(BUILD_DIR)/tb_am9513.vvp

tb_carbonio: $(BUILD_DIR)
	$(IVERILOG) $(IVERILOG_FLAGS) -o $(BUILD_DIR)/tb_carbonio.vvp $(COMMON_SV) $(CARBONIO_SV)
	$(VVP) $(BUILD_DIR)/tb_carbonio.vvp

tb_ez90_scaffold: $(BUILD_DIR)
	$(IVERILOG) $(IVERILOG_FLAGS) -o $(BUILD_DIR)/tb_ez90_scaffold.vvp $(COMMON_SV) $(EZ90_SV)
	$(VVP) $(BUILD_DIR)/tb_ez90_scaffold.vvp

tb_8096: $(BUILD_DIR)
	$(IVERILOG) $(IVERILOG_FLAGS) -o $(BUILD_DIR)/tb_8096.vvp $(COMMON_SV) $(X96_8096_SV)
	$(VVP) $(BUILD_DIR)/tb_8096.vvp

tb_8097: $(BUILD_DIR)
	$(IVERILOG) $(IVERILOG_FLAGS) -o $(BUILD_DIR)/tb_8097.vvp $(COMMON_SV) $(X96_8097_SV)
	$(VVP) $(BUILD_DIR)/tb_8097.vvp

tb_carbonz80: $(BUILD_DIR)
	$(IVERILOG) $(IVERILOG_FLAGS) -o $(BUILD_DIR)/tb_carbonz80.vvp $(COMMON_SV) $(CARBONZ80_SV)
	$(VVP) $(BUILD_DIR)/tb_carbonz80.vvp

tb_carbonz90: $(BUILD_DIR)
	$(IVERILOG) $(IVERILOG_FLAGS) -o $(BUILD_DIR)/tb_carbonz90.vvp $(COMMON_SV) $(CARBONZ90_SV)
	$(VVP) $(BUILD_DIR)/tb_carbonz90.vvp

tb_carbonez90: $(BUILD_DIR)
	$(IVERILOG) $(IVERILOG_FLAGS) -o $(BUILD_DIR)/tb_carbonez90.vvp $(COMMON_SV) $(CARBONEZ90_SV)
	$(VVP) $(BUILD_DIR)/tb_carbonez90.vvp

tb_carbonx86: $(BUILD_DIR)
	$(IVERILOG) $(IVERILOG_FLAGS) -o $(BUILD_DIR)/tb_carbonx86.vvp $(COMMON_SV) $(CARBONX86_SV)
	$(VVP) $(BUILD_DIR)/tb_carbonx86.vvp

tb_carbonx96: $(BUILD_DIR)
	$(IVERILOG) $(IVERILOG_FLAGS) -o $(BUILD_DIR)/tb_carbonx96.vvp $(COMMON_SV) $(CARBONX96_SV)
	$(VVP) $(BUILD_DIR)/tb_carbonx96.vvp

clean:
	rm -rf $(BUILD_DIR)
