// Project Carbon - Common Infrastructure
// fabric_addr_decode: Table-driven address-to-slave mapping.

module fabric_addr_decode #(
    parameter int unsigned N = 1,
    parameter int unsigned ADDR_W = 32,
    parameter int unsigned SLV_W = (N <= 1) ? 1 : $clog2(N),
    parameter bit HAS_DEFAULT = 1'b1,
    parameter int unsigned DEFAULT_SLAVE = 0,
    parameter logic [ADDR_W-1:0] SLAVE_BASE [N] = '{default: '0},
    parameter logic [ADDR_W-1:0] SLAVE_MASK [N] = '{default: '0}
) (
    input  logic [ADDR_W-1:0] addr,
    output logic              hit,
    output logic              decode_err,
    output logic [SLV_W-1:0]  slave_idx
);
  logic [SLV_W-1:0] idx_next;
  logic             hit_next;

  integer i;
  always_comb begin
    hit_next = 1'b0;
    idx_next = '0;
    for (i = 0; i < int'(N); i++) begin
      if (!hit_next) begin
        if ((addr & SLAVE_MASK[i]) == SLAVE_BASE[i]) begin
          hit_next = 1'b1;
          idx_next = SLV_W'(i);
        end
      end
    end

    if (hit_next) begin
      hit        = 1'b1;
      decode_err = 1'b0;
      slave_idx  = idx_next;
    end else if (HAS_DEFAULT) begin
      hit        = 1'b1;
      decode_err = 1'b0;
      slave_idx  = SLV_W'(DEFAULT_SLAVE);
    end else begin
      hit        = 1'b0;
      decode_err = 1'b1;
      slave_idx  = '0;
    end
  end

endmodule : fabric_addr_decode
