// Placeholder
// Project Carbon - 8096 CPU (8086-compatible subset, v1.0)
// cpu_8096: Top-level wrapper for the in-order x86-family core.

module cpu_8096 #(
    parameter int unsigned MODESTACK_DEPTH = carbon_arch_pkg::CARBON_MODESTACK_RECOMMENDED_DEPTH
) (
    input logic clk,
    input logic rst_n,

    fabric_if.master mem_if,
    fabric_if.master io_if,

    irq_if.sink irq,
    csr_if.slave csr,
    dbg_if.core dbg
);
  cpu_8096_core #(
      .MODESTACK_DEPTH(MODESTACK_DEPTH)
  ) u_core (
      .clk(clk),
      .rst_n(rst_n),
      .mem_if(mem_if),
      .io_if(io_if),
      .irq(irq),
      .csr(csr),
      .dbg(dbg)
  );

endmodule : cpu_8096
