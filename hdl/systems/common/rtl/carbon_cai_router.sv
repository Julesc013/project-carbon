// Project Carbon - Systems
// carbon_cai_router: Simple CAI link router (point-to-point, with optional overrides).

module carbon_cai_router #(
    parameter bit OVERRIDE_HOST_CFG = 1'b0,
    parameter logic [63:0] OVERRIDE_SUBMIT_DESC_BASE = 64'h0,
    parameter logic [31:0] OVERRIDE_SUBMIT_RING_MASK = 32'h0,
    parameter logic [15:0] OVERRIDE_CONTEXT_SEL      = 16'h0
) (
    cai_if cpu,
    cai_if dev
);
  // Host -> device
  always_comb begin
    dev.submit_desc_base =
        OVERRIDE_HOST_CFG ? OVERRIDE_SUBMIT_DESC_BASE : cpu.submit_desc_base;
    dev.submit_ring_mask =
        OVERRIDE_HOST_CFG ? OVERRIDE_SUBMIT_RING_MASK : cpu.submit_ring_mask;
    dev.context_sel =
        OVERRIDE_HOST_CFG ? OVERRIDE_CONTEXT_SEL : cpu.context_sel;
    dev.submit_doorbell = cpu.submit_doorbell;
  end

  // Device -> host
  always_comb begin
    cpu.comp_base     = dev.comp_base;
    cpu.comp_doorbell = dev.comp_doorbell;
    cpu.comp_irq      = dev.comp_irq;
    cpu.status        = dev.status;
  end

endmodule : carbon_cai_router

