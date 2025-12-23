# Project Carbon - Simulation runner (structure only)
#
# Intended usage (requires a simulator):
#   make tb_fabric_arbiter
#   make tb_irq_ctrl
#   make tb_ipi_mailbox
#   make tb_trace_ring
#   make tb_cai_contract
#   make tb_z85
#   make tb_z85_zex
#   make tb_z90
#   make tb_am9513_scalar
#   make tb_am9514_vector
#   make tb_am9515_tensor
#   make tb_z480_scaffold
#   make tb_z480_core_basic
#   make tb_8096
#   make tb_8097
#   make tb_carbonz80
#   make tb_carbonz90
#   make tb_carbonz480
#   make tb_carbonx86
#   make tb_carbonx96
#
# Uses Icarus Verilog if available.

SIM      ?= iverilog
IVERILOG ?= iverilog
VVP      ?= vvp
VERILATOR ?= verilator
VERILATOR_FLAGS ?= -Wall --binary --timing -sv

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

CARBONIO_RTL_SV := \
  ../cores/CarbonIO/rtl/carbonio_pkg.sv \
  ../cores/CarbonIO/rtl/carbonio_fifo.sv \
  ../cores/CarbonIO/rtl/carbonio_uart.sv \
  ../cores/CarbonIO/rtl/carbonio_pio.sv \
  ../cores/CarbonIO/rtl/carbonio_timer.sv \
  ../cores/CarbonIO/rtl/carbonio_irq_router.sv \
  ../cores/CarbonIO/rtl/carbonio.sv

CARBONIO_SV := \
  $(CARBONIO_RTL_SV) \
  ../cores/CarbonIO/tb/tb_carbonio.sv

CARBONDMA_RTL_SV := \
  ../cores/CarbonDMA/rtl/carbondma_pkg.sv \
  ../cores/CarbonDMA/rtl/carbondma.sv

CARBONDMA_SV := \
  $(CARBONDMA_RTL_SV) \
  ../cores/CarbonDMA/tb/tb_carbondma.sv

AM9513_RTL_SV := \
  ../cores/Am9513/rtl/am9513_pkg.sv \
  ../cores/Am9513/rtl/am9513_math_pkg.sv \
  ../cores/Am9513/rtl/am9511_compat.sv \
  ../cores/Am9513/rtl/am9512_compat.sv \
  ../cores/Am9513/rtl/am9513_scalar.sv \
  ../cores/Am9513/rtl/am9514_vector.sv \
  ../cores/Am9513/rtl/am9515_tensor.sv \
  ../cores/Am9513/rtl/am9513_context_file.sv \
  ../cores/Am9513/rtl/am9513_legacy_shell.sv \
  ../cores/Am9513/rtl/am9513_cai_engine.sv \
  ../cores/Am9513/rtl/am9513_accel.sv

AM9513_SCALAR_SV := \
  $(AM9513_RTL_SV) \
  ../cores/Am9513/tb/tb_am9513.sv

AM9514_VECTOR_SV := \
  $(AM9513_RTL_SV) \
  ../cores/Am9513/tb/tb_am9514_vector.sv

AM9515_TENSOR_SV := \
  $(AM9513_RTL_SV) \
  ../cores/Am9513/tb/tb_am9515_tensor.sv

Z480_SV := \
  ../cores/Z480/rtl/z480_pkg.sv \
  ../cores/Z480/rtl/uop_queue.sv \
  ../cores/Z480/rtl/fe_bpred.sv \
  ../cores/Z480/rtl/fe_icache_port.sv \
  ../cores/Z480/rtl/fe_fetch.sv \
  ../cores/Z480/rtl/fe_decode.sv \
  ../cores/Z480/rtl/fe_uop_cache.sv \
  ../cores/Z480/rtl/renamer.sv \
  ../cores/Z480/rtl/dispatch.sv \
  ../cores/Z480/rtl/rob.sv \
  ../cores/Z480/rtl/rs_int.sv \
  ../cores/Z480/rtl/lsq.sv \
  ../cores/Z480/rtl/scheduler.sv \
  ../cores/Z480/rtl/exec_int_alu.sv \
  ../cores/Z480/rtl/exec_branch.sv \
  ../cores/Z480/rtl/exec_muldiv.sv \
  ../cores/Z480/rtl/exec_vec.sv \
  ../cores/Z480/rtl/writeback.sv \
  ../cores/Z480/rtl/commit.sv \
  ../cores/Z480/rtl/priv_ctrl.sv \
  ../cores/Z480/rtl/mmu.sv \
  ../cores/Z480/rtl/trap_unit.sv \
  ../cores/Z480/rtl/iommu_hook.sv \
  ../cores/Z480/rtl/icache_port.sv \
  ../cores/Z480/rtl/dcache_port.sv \
  ../cores/Z480/rtl/cpuid_block.sv \
  ../cores/Z480/rtl/z480_core.sv \
  ../cores/Z480/tb/tb_z480_scaffold.sv

Z480_RTL_SV := \
  ../cores/Z480/rtl/z480_pkg.sv \
  ../cores/Z480/rtl/uop_queue.sv \
  ../cores/Z480/rtl/fe_bpred.sv \
  ../cores/Z480/rtl/fe_icache_port.sv \
  ../cores/Z480/rtl/fe_fetch.sv \
  ../cores/Z480/rtl/fe_decode.sv \
  ../cores/Z480/rtl/fe_uop_cache.sv \
  ../cores/Z480/rtl/renamer.sv \
  ../cores/Z480/rtl/dispatch.sv \
  ../cores/Z480/rtl/rob.sv \
  ../cores/Z480/rtl/rs_int.sv \
  ../cores/Z480/rtl/lsq.sv \
  ../cores/Z480/rtl/scheduler.sv \
  ../cores/Z480/rtl/exec_int_alu.sv \
  ../cores/Z480/rtl/exec_branch.sv \
  ../cores/Z480/rtl/exec_muldiv.sv \
  ../cores/Z480/rtl/exec_vec.sv \
  ../cores/Z480/rtl/writeback.sv \
  ../cores/Z480/rtl/commit.sv \
  ../cores/Z480/rtl/priv_ctrl.sv \
  ../cores/Z480/rtl/mmu.sv \
  ../cores/Z480/rtl/trap_unit.sv \
  ../cores/Z480/rtl/iommu_hook.sv \
  ../cores/Z480/rtl/icache_port.sv \
  ../cores/Z480/rtl/dcache_port.sv \
  ../cores/Z480/rtl/cpuid_block.sv \
  ../cores/Z480/rtl/z480_core.sv

Z480_CORE_BASIC_SV := \
  $(Z480_RTL_SV) \
  ../cores/Z480/tb/tb_z480_core_basic.sv

Z85_RTL_SV := \
  ../cores/Z85/rtl/z85_regfile.sv \
  ../cores/Z85/rtl/z85_flags.sv \
  ../cores/Z85/rtl/z85_decode.sv \
  ../cores/Z85/rtl/z85_core.sv

Z85_SV := \
  $(Z85_RTL_SV) \
  ../cores/Z85/ref/z85_ref_model.sv \
  ../cores/Z85/tb/tb_z85.sv

Z85_ZEX_SV := \
  $(Z85_RTL_SV) \
  ../cores/Z85/ref/z85_ref_model.sv \
  ../cores/Z85/tb/tb_z85.sv \
  ../cores/Z85/tb/tb_z85_zex.sv

Z90_RTL_SV := \
  $(Z85_RTL_SV) \
  ../cores/Z90/rtl/z90_decode_pkg.sv \
  ../cores/Z90/rtl/z90_alu_pkg.sv \
  ../cores/Z90/rtl/z90_core.sv

Z90_SV := \
  $(Z90_RTL_SV) \
  ../cores/Z90/tb/tb_z90.sv

Z380_RTL_SV := \
  $(Z85_RTL_SV) \
  ../cores/Z380/rtl/z380_core.sv

Z380_PLATFORM_SV := \
  ../uncore/Z380_platform/rtl/z380_chipselect.sv \
  ../uncore/Z380_platform/rtl/z380_waitgen.sv \
  ../uncore/Z380_platform/rtl/z380_dram_refresh.sv

X96_8096_RTL_SV := \
  ../cores/8096/rtl/cpu_8096_pkg.sv \
  ../cores/8096/rtl/cpu_8096_core.sv \
  ../cores/8096/rtl/cpu_8096.sv

X96_8097_RTL_SV := \
  ../cores/Am9513/rtl/am9513_math_pkg.sv \
  ../cores/8097/rtl/fpu_8097_pkg.sv \
  ../cores/8097/rtl/fpu_8097.sv

SYSTEMS_COMMON_SV := \
  $(CARBONIO_RTL_SV) \
  $(CARBONDMA_RTL_SV) \
  ../systems/common/rtl/carbon_memmap_pkg.sv \
  ../systems/common/rtl/carbon_bootrom.sv \
  ../systems/common/rtl/carbon_sram.sv \
  ../systems/common/rtl/carbon_mmio_regs.sv \
  ../systems/common/rtl/carbon_cai_router.sv \
  ../systems/common/rtl/carbon_csr_master_simple.sv \
  ../systems/common/rtl/carbon_fabric_bootmaster.sv \
  ../systems/common/rtl/z80_bus_adapter_stub.sv \
  ../systems/common/rtl/x86_bus_adapter_stub.sv \
  ../systems/common/rtl/tier_host_ctrl.sv \
  ../systems/common/rtl/csr_master_tieoff.sv \
  ../systems/common/rtl/dbg_hub_tieoff.sv \
  ../systems/common/rtl/irq_src_tieoff.sv \
  ../systems/common/rtl/cai_host_tieoff.sv

CARBONZ80_RTL_SV := \
  $(SYSTEMS_COMMON_SV) \
  $(Z85_RTL_SV) \
  $(AM9513_RTL_SV) \
  ../systems/CarbonZ80/rtl/carbonz80_top.sv

CARBONZ80_SV := \
  $(CARBONZ80_RTL_SV) \
  ../systems/CarbonZ80/tb/tb_carbonz80.sv

CARBONZ80_TIERS_SV := \
  $(CARBONZ80_RTL_SV) \
  ../systems/CarbonZ80/tb/tb_carbonz80_tiers.sv

CARBONZ90_RTL_SV := \
  $(SYSTEMS_COMMON_SV) \
  $(Z90_RTL_SV) \
  $(AM9513_RTL_SV) \
  ../systems/CarbonZ90/rtl/carbonz90_top.sv

CARBONZ90_SV := \
  $(CARBONZ90_RTL_SV) \
  ../systems/CarbonZ90/tb/tb_carbonz90.sv

CARBONZ90_TIERS_SV := \
  $(CARBONZ90_RTL_SV) \
  ../systems/CarbonZ90/tb/tb_carbonz90_tiers.sv

CARBONZ380_RTL_SV := \
  $(SYSTEMS_COMMON_SV) \
  $(Z380_RTL_SV) \
  $(Z380_PLATFORM_SV) \
  $(AM9513_RTL_SV) \
  ../systems/CarbonZ380/rtl/carbonz380_top.sv

CARBONZ380_SMOKE_SV := \
  $(CARBONZ380_RTL_SV) \
  ../systems/CarbonZ380/tb/tb_carbonz380_smoke.sv

CARBONZ380_TIERS_SV := \
  $(CARBONZ380_RTL_SV) \
  ../systems/CarbonZ380/tb/tb_carbonz380_tiers.sv

CARBONZ480_RTL_SV := \
  $(SYSTEMS_COMMON_SV) \
  $(Z480_RTL_SV) \
  $(AM9513_RTL_SV) \
  ../systems/CarbonZ480/rtl/carbonz480_top.sv

CARBONZ480_SV := \
  $(CARBONZ480_RTL_SV) \
  ../systems/CarbonZ480/tb/tb_carbonz480.sv

CARBONZ480_SMOKE_SV := \
  $(CARBONZ480_RTL_SV) \
  ../systems/CarbonZ480/tb/tb_carbonz480_smoke.sv

TIER_HOST_SV := \
  $(SYSTEMS_COMMON_SV) \
  ../systems/common/tb/tb_tier_host_ctrl.sv

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

ifeq ($(SIM),verilator)
define run_tb
        mkdir -p $(BUILD_DIR)/verilator/$1
        $(VERILATOR) $(VERILATOR_FLAGS) --top-module $1 -Mdir $(BUILD_DIR)/verilator/$1 -o $(BUILD_DIR)/verilator/$1/$1 $2
        $(BUILD_DIR)/verilator/$1/$1
endef
else
define run_tb
	$(IVERILOG) $(IVERILOG_FLAGS) -o $(BUILD_DIR)/$1.vvp $2
	$(VVP) $(BUILD_DIR)/$1.vvp
endef
endif

.PHONY: all clean tb_fabric_contract tb_csr_contract tb_irq_contract tb_fabric_arbiter tb_irq_ctrl tb_ipi_mailbox tb_trace_ring tb_cai_contract tb_z85 tb_z85_zex tb_z90 tb_am9513 tb_am9513_scalar tb_am9514_vector tb_am9515_tensor tb_carbonio tb_carbondma tb_z480_scaffold tb_z480_core_basic tb_8096 tb_8097 tb_carbonz80 tb_carbonz80_tiers tb_carbonz90 tb_carbonz90_tiers tb_carbonz380_smoke tb_carbonz380_tiers tb_carbonz480 tb_carbonz480_smoke tb_tier_host_ctrl tb_carbonx86 tb_carbonx96
all: tb_fabric_contract tb_csr_contract tb_irq_contract tb_fabric_arbiter tb_irq_ctrl tb_ipi_mailbox tb_trace_ring tb_cai_contract tb_z85 tb_z90 tb_am9513_scalar tb_am9514_vector tb_am9515_tensor tb_z480_scaffold tb_z480_core_basic tb_8096 tb_8097 tb_carbonz80 tb_carbonz80_tiers tb_carbonz90 tb_carbonz90_tiers tb_carbonz380_smoke tb_carbonz380_tiers tb_carbonz480 tb_carbonz480_smoke tb_tier_host_ctrl tb_carbonx86 tb_carbonx96

$(BUILD_DIR):
	mkdir -p $(BUILD_DIR)

tb_fabric_arbiter: $(BUILD_DIR)
	$(call run_tb,tb_fabric_arbiter,$(COMMON_SV) tb/tb_fabric_arbiter.sv)

tb_fabric_contract: $(BUILD_DIR)
	$(call run_tb,tb_fabric_contract,$(COMMON_SV) tb/tb_fabric_contract.sv)

tb_csr_contract: $(BUILD_DIR)
	$(call run_tb,tb_csr_contract,$(COMMON_SV) tb/tb_csr_contract.sv)

tb_irq_contract: $(BUILD_DIR)
	$(call run_tb,tb_irq_contract,$(COMMON_SV) tb/tb_irq_contract.sv)

tb_irq_ctrl: $(BUILD_DIR)
	$(call run_tb,tb_irq_ctrl,$(COMMON_SV) tb/tb_irq_ctrl.sv)

tb_ipi_mailbox: $(BUILD_DIR)
	$(call run_tb,tb_ipi_mailbox,$(COMMON_SV) tb/tb_ipi_mailbox.sv)

tb_trace_ring: $(BUILD_DIR)
	$(call run_tb,tb_trace_ring,$(COMMON_SV) tb/tb_trace_ring.sv)

tb_cai_contract: $(BUILD_DIR)
	$(call run_tb,tb_cai_contract,$(COMMON_SV) $(AM9513_RTL_SV) tb/tb_cai_contract.sv)

tb_z85: $(BUILD_DIR)
	$(call run_tb,tb_z85,$(COMMON_SV) $(Z85_SV))

tb_z85_zex: $(BUILD_DIR)
	$(call run_tb,tb_z85_zex,$(COMMON_SV) $(Z85_ZEX_SV))

tb_z90: $(BUILD_DIR)
	$(call run_tb,tb_z90,$(COMMON_SV) $(Z90_SV))

tb_am9513_scalar: $(BUILD_DIR)
	$(call run_tb,tb_am9513_scalar,$(COMMON_SV) $(AM9513_SCALAR_SV))

tb_am9514_vector: $(BUILD_DIR)
	$(call run_tb,tb_am9514_vector,$(COMMON_SV) $(AM9514_VECTOR_SV))

tb_am9515_tensor: $(BUILD_DIR)
	$(call run_tb,tb_am9515_tensor,$(COMMON_SV) $(AM9515_TENSOR_SV))

tb_am9513: tb_am9513_scalar

tb_carbonio: $(BUILD_DIR)
	$(call run_tb,tb_carbonio,$(COMMON_SV) $(CARBONIO_SV))

tb_carbondma: $(BUILD_DIR)
	$(call run_tb,tb_carbondma,$(COMMON_SV) $(CARBONDMA_SV))

tb_z480_scaffold: $(BUILD_DIR)
	$(call run_tb,tb_z480_scaffold,$(COMMON_SV) $(Z480_SV))

tb_z480_core_basic: $(BUILD_DIR)
	$(call run_tb,tb_z480_core_basic,$(COMMON_SV) $(Z480_CORE_BASIC_SV))

tb_8096: $(BUILD_DIR)
	$(call run_tb,tb_8096,$(COMMON_SV) $(X96_8096_SV))

tb_8097: $(BUILD_DIR)
	$(call run_tb,tb_8097,$(COMMON_SV) $(X96_8097_SV))

tb_carbonz80: $(BUILD_DIR)
	$(call run_tb,tb_carbonz80,$(COMMON_SV) $(CARBONZ80_SV))

tb_carbonz80_tiers: $(BUILD_DIR)
	$(call run_tb,tb_carbonz80_tiers,$(COMMON_SV) $(CARBONZ80_TIERS_SV))

tb_carbonz90: $(BUILD_DIR)
	$(call run_tb,tb_carbonz90,$(COMMON_SV) $(CARBONZ90_SV))

tb_carbonz90_tiers: $(BUILD_DIR)
	$(call run_tb,tb_carbonz90_tiers,$(COMMON_SV) $(CARBONZ90_TIERS_SV))

tb_carbonz380_smoke: $(BUILD_DIR)
	$(call run_tb,tb_carbonz380_smoke,$(COMMON_SV) $(CARBONZ380_SMOKE_SV))

tb_carbonz380_tiers: $(BUILD_DIR)
	$(call run_tb,tb_carbonz380_tiers,$(COMMON_SV) $(CARBONZ380_TIERS_SV))

tb_carbonz480: $(BUILD_DIR)
	$(call run_tb,tb_carbonz480,$(COMMON_SV) $(CARBONZ480_SV))

tb_carbonz480_smoke: $(BUILD_DIR)
	$(call run_tb,tb_carbonz480_smoke,$(COMMON_SV) $(CARBONZ480_SMOKE_SV))

tb_tier_host_ctrl: $(BUILD_DIR)
	$(call run_tb,tb_tier_host_ctrl,$(COMMON_SV) $(TIER_HOST_SV))

tb_carbonx86: $(BUILD_DIR)
	$(call run_tb,tb_carbonx86,$(COMMON_SV) $(CARBONX86_SV))

tb_carbonx96: $(BUILD_DIR)
	$(call run_tb,tb_carbonx96,$(COMMON_SV) $(CARBONX96_SV))

clean:
	rm -rf $(BUILD_DIR)
