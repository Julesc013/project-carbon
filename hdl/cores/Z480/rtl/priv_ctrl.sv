// Project Carbon - Z480 P7 core scaffold
// priv_ctrl: Privilege framework scaffolding (U/S/H + interrupt enable/pending).

module priv_ctrl #(
    parameter int unsigned IRQ_N = 32
) (
    input logic clk,
    input logic rst_n,

    // Privilege mode control (future ISA hooks)
    input  logic               set_priv_valid,
    input  z480_pkg::z480_priv_e set_priv_mode,
    output z480_pkg::z480_priv_e priv_mode,

    // Trap vector base registers (future CSRs)
    input  logic        tv_u_we,
    input  logic [63:0] tv_u_wdata,
    output logic [63:0] tv_u_base,

    input  logic        tv_s_we,
    input  logic [63:0] tv_s_wdata,
    output logic [63:0] tv_s_base,

    input  logic        tv_h_we,
    input  logic [63:0] tv_h_wdata,
    output logic [63:0] tv_h_base,

    // Interrupt enable (CSR_IE) and pending snapshot (CSR_IP)
    input  logic              ie_we,
    input  logic [IRQ_N-1:0]   ie_wdata,
    output logic [IRQ_N-1:0]   ie,

    input  logic [IRQ_N-1:0]   irq_pending_in,
    output logic [IRQ_N-1:0]   ip,

    output logic              irq_any_pending
);
  import z480_pkg::*;

  z480_priv_e priv_mode_q;
  logic [63:0] tv_u_q, tv_s_q, tv_h_q;
  logic [IRQ_N-1:0] ie_q;
  logic [IRQ_N-1:0] ip_q;

  assign priv_mode = priv_mode_q;
  assign tv_u_base = tv_u_q;
  assign tv_s_base = tv_s_q;
  assign tv_h_base = tv_h_q;
  assign ie = ie_q;
  assign ip = ip_q;

  assign irq_any_pending = |(ie_q & ip_q);

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      priv_mode_q <= Z480_PRIV_S;
      tv_u_q <= 64'h0;
      tv_s_q <= 64'h0;
      tv_h_q <= 64'h0;
      ie_q   <= '0;
      ip_q   <= '0;
    end else begin
      ip_q <= irq_pending_in;

      if (set_priv_valid) begin
        priv_mode_q <= set_priv_mode;
      end

      if (tv_u_we) tv_u_q <= tv_u_wdata;
      if (tv_s_we) tv_s_q <= tv_s_wdata;
      if (tv_h_we) tv_h_q <= tv_h_wdata;

      if (ie_we) ie_q <= ie_wdata;
    end
  end

endmodule : priv_ctrl
