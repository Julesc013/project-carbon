// Project Carbon - Common Infrastructure
// fabric_crossbar_1x1: 1 master <-> 1 slave pass-through with optional decode_err injection.
//
// For simplicity/correctness, this implementation allows at most one in-flight transaction.

module fabric_crossbar_1x1 #(
    parameter int unsigned ADDR_W = 32,
    parameter int unsigned DATA_W = 32,
    parameter int unsigned ID_W   = 4,
    parameter int unsigned OP_W   = 8,
    parameter int unsigned SIZE_W = 3,
    parameter int unsigned ATTR_W = carbon_arch_pkg::CARBON_FABRIC_ATTR_WIDTH_BITS,
    parameter int unsigned CODE_W = 8,

    parameter bit ADDR_DECODE_EN = 1'b0,
    parameter logic [ADDR_W-1:0] ADDR_BASE = '0,
    parameter logic [ADDR_W-1:0] ADDR_MASK = '0
) (
    input logic clk,
    input logic rst_n,
    fabric_if #(
        .ADDR_W(ADDR_W),
        .DATA_W(DATA_W),
        .ID_W(ID_W),
        .OP_W(OP_W),
        .SIZE_W(SIZE_W),
        .ATTR_W(ATTR_W),
        .CODE_W(CODE_W)
    ).slave up,
    fabric_if #(
        .ADDR_W(ADDR_W),
        .DATA_W(DATA_W),
        .ID_W(ID_W),
        .OP_W(OP_W),
        .SIZE_W(SIZE_W),
        .ATTR_W(ATTR_W),
        .CODE_W(CODE_W)
    ).master dn
);
  import carbon_arch_pkg::*;

  typedef enum logic [0:0] {ST_IDLE, ST_WAIT_RSP} state_t;
  state_t state_q;

  logic inflight_err_q;
  logic [ID_W-1:0] inflight_id_q;

  logic in_range;
  assign in_range = (!ADDR_DECODE_EN) || ((up.req_addr & ADDR_MASK) == ADDR_BASE);

  // Combinational datapath defaults.
  always_comb begin
    // Default: no request forwarded.
    dn.req_valid = 1'b0;
    dn.req_op    = '0;
    dn.req_addr  = '0;
    dn.req_wdata = '0;
    dn.req_wstrb = '0;
    dn.req_size  = '0;
    dn.req_attr  = '0;
    dn.req_id    = '0;

    // Default: no response to upstream.
    up.rsp_valid = 1'b0;
    up.rsp_rdata = '0;
    up.rsp_code  = '0;
    up.rsp_id    = '0;

    // Default: apply backpressure.
    up.req_ready = 1'b0;
    dn.rsp_ready = 1'b0;

    unique case (state_q)
      ST_IDLE: begin
        if (in_range) begin
          dn.req_valid = up.req_valid;
          dn.req_op    = up.req_op;
          dn.req_addr  = up.req_addr;
          dn.req_wdata = up.req_wdata;
          dn.req_wstrb = up.req_wstrb;
          dn.req_size  = up.req_size;
          dn.req_attr  = up.req_attr;
          dn.req_id    = up.req_id;

          up.req_ready = dn.req_ready;

          // Pass through any downstream response (may be 0-latency).
          up.rsp_valid = dn.rsp_valid;
          up.rsp_rdata = dn.rsp_rdata;
          up.rsp_code  = dn.rsp_code;
          up.rsp_id    = dn.rsp_id;
          dn.rsp_ready = up.rsp_ready;
        end else begin
          // Out-of-range request: accept and respond with decode_err.
          up.req_ready = 1'b1;
        end
      end

      ST_WAIT_RSP: begin
        if (inflight_err_q) begin
          up.rsp_valid = 1'b1;
          up.rsp_rdata = '0;
          up.rsp_code  = CODE_W'(CARBON_FABRIC_RESP_DECODE_ERR);
          up.rsp_id    = inflight_id_q;
        end else begin
          up.rsp_valid = dn.rsp_valid;
          up.rsp_rdata = dn.rsp_rdata;
          up.rsp_code  = dn.rsp_code;
          up.rsp_id    = dn.rsp_id;
          dn.rsp_ready = up.rsp_ready;
        end
      end
      default: begin
      end
    endcase
  end

  wire req_fire = up.req_valid && up.req_ready;
  wire rsp_fire_up = up.rsp_valid && up.rsp_ready;
  wire rsp_fire_dn = dn.rsp_valid && dn.rsp_ready;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      state_q       <= ST_IDLE;
      inflight_err_q <= 1'b0;
      inflight_id_q  <= '0;
    end else begin
      unique case (state_q)
        ST_IDLE: begin
          if (req_fire) begin
            if (in_range) begin
              // If a 0-latency response was accepted the same cycle, remain idle.
              if (rsp_fire_dn) begin
                state_q <= ST_IDLE;
              end else begin
                state_q       <= ST_WAIT_RSP;
                inflight_err_q <= 1'b0;
              end
            end else begin
              state_q       <= ST_WAIT_RSP;
              inflight_err_q <= 1'b1;
              inflight_id_q  <= up.req_id;
            end
          end
        end

        ST_WAIT_RSP: begin
          if (inflight_err_q) begin
            if (rsp_fire_up) begin
              state_q       <= ST_IDLE;
              inflight_err_q <= 1'b0;
            end
          end else begin
            if (rsp_fire_dn) begin
              state_q <= ST_IDLE;
            end
          end
        end
        default: begin
          state_q <= ST_IDLE;
        end
      endcase
    end
  end

endmodule : fabric_crossbar_1x1
