// Project Carbon - Z480 P7 core scaffold
// trap_unit: Trap state scaffolding (cause/EPC + return hooks).

module trap_unit (
    input logic clk,
    input logic rst_n,

    // Trap raise hook (from commit/execute)
    input  logic        raise_valid,
    input  logic [31:0] raise_cause,
    input  logic [63:0] raise_epc,

    // Trap return hooks (future ISA: SRET/HRET)
    input  logic sret,
    input  logic hret,

    // CSR write hook for EPC (privileged)
    input  logic        epc_we,
    input  logic [31:0] epc_wdata,

    output logic        in_trap,
    output logic [31:0] cause,
    output logic [63:0] epc,
    output logic        ret_valid,
    output logic [63:0] ret_pc
);
  logic in_trap_q;
  logic [31:0] cause_q;
  logic [63:0] epc_q;

  assign in_trap = in_trap_q;
  assign cause   = cause_q;
  assign epc     = epc_q;

  assign ret_valid = (sret || hret);
  assign ret_pc    = epc_q;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      in_trap_q <= 1'b0;
      cause_q   <= 32'h0;
      epc_q     <= 64'h0;
    end else begin
      if (raise_valid) begin
        in_trap_q <= 1'b1;
        cause_q   <= raise_cause;
        epc_q     <= raise_epc;
      end else if (sret || hret) begin
        in_trap_q <= 1'b0;
        cause_q   <= 32'h0;
      end

      if (epc_we) begin
        epc_q[31:0]  <= epc_wdata;
        epc_q[63:32] <= 32'h0;
      end
    end
  end

endmodule : trap_unit
