# Project Carbon - Simulation runner (structure only)
#
# Intended usage (requires a simulator):
#   make tb_fabric_arbiter
#   make tb_irq_ctrl
#   make tb_ipi_mailbox
#   make tb_trace_ring
#   make tb_am9513
#   make tb_ez90_scaffold
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

AM9513_SV := \
  ../cores/Am9513/rtl/am9513_pkg.sv \
  ../cores/Am9513/rtl/am9513_math_pkg.sv \
  ../cores/Am9513/rtl/am9513_context_file.sv \
  ../cores/Am9513/rtl/am9513_legacy_shell.sv \
  ../cores/Am9513/rtl/am9513_cai_engine.sv \
  ../cores/Am9513/rtl/am9513_accel.sv \
  ../cores/Am9513/tb/tb_am9513.sv

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

IVERILOG_FLAGS := -g2012 -Wall -Wno-timescale

.PHONY: all clean tb_fabric_arbiter tb_irq_ctrl tb_ipi_mailbox tb_trace_ring tb_am9513 tb_ez90_scaffold
all: tb_fabric_arbiter tb_irq_ctrl tb_ipi_mailbox tb_trace_ring tb_am9513 tb_ez90_scaffold

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

tb_am9513: $(BUILD_DIR)
	$(IVERILOG) $(IVERILOG_FLAGS) -o $(BUILD_DIR)/tb_am9513.vvp $(COMMON_SV) $(AM9513_SV)
	$(VVP) $(BUILD_DIR)/tb_am9513.vvp

tb_ez90_scaffold: $(BUILD_DIR)
	$(IVERILOG) $(IVERILOG_FLAGS) -o $(BUILD_DIR)/tb_ez90_scaffold.vvp $(COMMON_SV) $(EZ90_SV)
	$(VVP) $(BUILD_DIR)/tb_ez90_scaffold.vvp

clean:
	rm -rf $(BUILD_DIR)
