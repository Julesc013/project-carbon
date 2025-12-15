# Project Carbon - Simulation runner (structure only)
#
# Intended usage (requires a simulator):
#   make tb_fabric_arbiter
#   make tb_irq_ctrl
#   make tb_ipi_mailbox
#   make tb_trace_ring
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

IVERILOG_FLAGS := -g2012 -Wall -Wno-timescale

.PHONY: all clean tb_fabric_arbiter tb_irq_ctrl tb_ipi_mailbox tb_trace_ring
all: tb_fabric_arbiter tb_irq_ctrl tb_ipi_mailbox tb_trace_ring

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

clean:
	rm -rf $(BUILD_DIR)

