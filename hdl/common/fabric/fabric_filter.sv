// Project Carbon - Common Infrastructure
// fabric_filter: Optional fabric request filter with attr enforcement and deny ranges.
//
// Notes:
// - One in-flight transaction at a time (like fabric_crossbar_1x1).
// - IO attribute enforcement can coerce ordered+uncached semantics.
// - Deny ranges return DECODE_ERR without forwarding downstream.
// - Placeholder for future IOMMU integration.

module fabric_filter #(
    parameter int unsigned ADDR_W = 32,
    parameter int unsigned DATA_W = 32,
    parameter int unsigned ID_W   = 4,
    parameter int unsigned OP_W   = 8,
    parameter int unsigned SIZE_W = 3,
    parameter int unsigned ATTR_W = carbon_arch_pkg::CARBON_FABRIC_ATTR_WIDTH_BITS,
    parameter int unsigned CODE_W = 8,

    parameter bit ENFORCE_IO_ORDERED_UNCACHED = 1'b1,
    parameter bit DENY_EN = 1'b0,
    parameter int unsigned DENY_COUNT = 0,
    parameter logic [DENY_COUNT*ADDR_W-1:0] DENY_BASE = '0,
    parameter logic [DENY_COUNT*ADDR_W-1:0] DENY_MASK = '0,
    parameter bit IOMMU_EN = 1'b0
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

  function automatic logic [ADDR_W-1:0] deny_base_at(input int unsigned idx);
    deny_base_at = DENY_BASE[idx*ADDR_W +: ADDR_W];
  endfunction

  function automatic logic [ADDR_W-1:0] deny_mask_at(input int unsigned idx);
    deny_mask_at = DENY_MASK[idx*ADDR_W +: ADDR_W];
  endfunction

  function automatic logic deny_hit(input logic [ADDR_W-1:0] addr);
    int unsigned i;
    begin
      deny_hit = 1'b0;
      if (DENY_EN) begin
        for (i = 0; i < int'(DENY_COUNT); i++) begin
          if ((addr & deny_mask_at(i)) == deny_base_at(i)) begin
            deny_hit = 1'b1;
          end
        end
      end
    end
  endfunction

  function automatic logic [ATTR_W-1:0] enforce_io_attr(
      input logic [ATTR_W-1:0] attr
  );
    logic [ATTR_W-1:0] v;
    begin
      v = attr;
      if (ENFORCE_IO_ORDERED_UNCACHED &&
          ((attr & logic [ATTR_W-1:0]'(CARBON_MEM_ATTR_IO_SPACE_MASK)) != '0)) begin
        v &= ~logic [ATTR_W-1:0]'(CARBON_MEM_ATTR_CACHEABLE_MASK);
        v |= logic [ATTR_W-1:0]'(CARBON_MEM_ATTR_ORDERED_MASK);
      end
      enforce_io_attr = v;
    end
  endfunction

  // TODO: IOMMU integration hook (translate addr/attr, set fault).
  // When IOMMU_EN is enabled, apply translation before deny/forwarding.
  wire _unused_iommu = IOMMU_EN;

  typedef enum logic [0:0] {ST_IDLE, ST_WAIT_RSP} state_t;
  state_t state_q;

  logic inflight_err_q;
  logic [ID_W-1:0] inflight_id_q;

  wire deny_req = deny_hit(up.req_addr);
  wire [ATTR_W-1:0] eff_attr = enforce_io_attr(up.req_attr);

  always_comb begin
    dn.req_valid = 1'b0;
    dn.req_op    = '0;
    dn.req_addr  = '0;
    dn.req_wdata = '0;
    dn.req_wstrb = '0;
    dn.req_size  = '0;
    dn.req_attr  = '0;
    dn.req_id    = '0;

    up.rsp_valid = 1'b0;
    up.rsp_rdata = '0;
    up.rsp_code  = '0;
    up.rsp_id    = '0;

    up.req_ready = 1'b0;
    dn.rsp_ready = 1'b0;

    unique case (state_q)
      ST_IDLE: begin
        if (!deny_req) begin
          dn.req_valid = up.req_valid;
          dn.req_op    = up.req_op;
          dn.req_addr  = up.req_addr;
          dn.req_wdata = up.req_wdata;
          dn.req_wstrb = up.req_wstrb;
          dn.req_size  = up.req_size;
          dn.req_attr  = eff_attr;
          dn.req_id    = up.req_id;

          up.req_ready = dn.req_ready;

          // Pass through any downstream response (may be 0-latency).
          up.rsp_valid = dn.rsp_valid;
          up.rsp_rdata = dn.rsp_rdata;
          up.rsp_code  = dn.rsp_code;
          up.rsp_id    = dn.rsp_id;
          dn.rsp_ready = up.rsp_ready;
        end else begin
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
            if (deny_req) begin
              state_q       <= ST_WAIT_RSP;
              inflight_err_q <= 1'b1;
              inflight_id_q  <= up.req_id;
            end else if (rsp_fire_dn) begin
              state_q       <= ST_IDLE;
              inflight_err_q <= 1'b0;
            end else begin
              state_q       <= ST_WAIT_RSP;
              inflight_err_q <= 1'b0;
            end
          end
        end

        ST_WAIT_RSP: begin
          if (inflight_err_q) begin
            if (rsp_fire_up) begin
              state_q       <= ST_IDLE;
              inflight_err_q <= 1'b0;
            end
          end else if (rsp_fire_dn) begin
            state_q <= ST_IDLE;
          end
        end
        default: state_q <= ST_IDLE;
      endcase
    end
  end

endmodule : fabric_filter
