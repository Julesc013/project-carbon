// Project Carbon - Systems
// carbon_fabric_bootmaster: Minimal fabric master that writes a signature and powers off.

module carbon_fabric_bootmaster #(
    parameter logic [31:0] MMIO_BASE   = 32'h0000_0000,
    parameter logic [31:0] SIGNATURE   = 32'h0000_0000,
    parameter int unsigned START_DELAY = 8
) (
    input logic clk,
    input logic rst_n,
    fabric_if.master fab,
    output logic done
);
  import carbon_arch_pkg::*;
  import carbon_memmap_pkg::*;

  localparam int unsigned FAB_ADDR_W = $bits(fab.req_addr);
  localparam int unsigned FAB_DATA_W = $bits(fab.req_wdata);
  localparam int unsigned FAB_STRB_W = $bits(fab.req_wstrb);
  localparam int unsigned FAB_OP_W   = $bits(fab.req_op);
  localparam int unsigned FAB_ATTR_W = $bits(fab.req_attr);
  localparam int unsigned FAB_ID_W   = $bits(fab.req_id);
  localparam int unsigned FAB_CODE_W = $bits(fab.rsp_code);

  typedef enum logic [2:0] {
    ST_DELAY,
    ST_SIG_REQ,
    ST_SIG_RSP,
    ST_POFF_REQ,
    ST_POFF_RSP,
    ST_DONE
  } st_e;

  st_e st_q;
  logic [$clog2(START_DELAY+1)-1:0] delay_q;

  // Default: ordered, cacheable is fine for a simple bring-up master.
  localparam logic [FAB_ATTR_W-1:0] ATTR =
      FAB_ATTR_W'(CARBON_MEM_ATTR_ORDERED_MASK | CARBON_MEM_ATTR_CACHEABLE_MASK);

  // Drive outputs.
  assign fab.rsp_ready = 1'b1;
  assign done = (st_q == ST_DONE);

  // Request defaults (overridden per state).
  always_comb begin
    fab.req_valid = 1'b0;
    fab.req_op    = FAB_OP_W'(CARBON_FABRIC_XACT_WRITE);
    fab.req_addr  = '0;
    fab.req_wdata = '0;
    fab.req_wstrb = '0;
    fab.req_size  = '0;
    fab.req_attr  = ATTR;
    fab.req_id    = FAB_ID_W'(0);

    unique case (st_q)
      ST_SIG_REQ: begin
        fab.req_valid = 1'b1;
        fab.req_addr  = FAB_ADDR_W'(MMIO_BASE + CARBON_MMIO_SIGNATURE_OFF);
        fab.req_wdata = FAB_DATA_W'(SIGNATURE);
        fab.req_wstrb = '1;
      end
      ST_POFF_REQ: begin
        fab.req_valid = 1'b1;
        fab.req_addr  = FAB_ADDR_W'(MMIO_BASE + CARBON_MMIO_POWEROFF_OFF);
        fab.req_wdata = FAB_DATA_W'(32'h0000_0001);
        fab.req_wstrb = '0;
        fab.req_wstrb[0] = 1'b1;
      end
      default: begin
      end
    endcase
  end

  wire req_fire = fab.req_valid && fab.req_ready;
  wire rsp_fire = fab.rsp_valid && fab.rsp_ready;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      st_q <= ST_DELAY;
      delay_q <= $clog2(START_DELAY+1)'(START_DELAY);
    end else begin
      unique case (st_q)
        ST_DELAY: begin
          if (delay_q == 0) st_q <= ST_SIG_REQ;
          else delay_q <= delay_q - 1'b1;
        end
        ST_SIG_REQ: begin
          if (req_fire) st_q <= ST_SIG_RSP;
        end
        ST_SIG_RSP: begin
          if (rsp_fire) st_q <= ST_POFF_REQ;
        end
        ST_POFF_REQ: begin
          if (req_fire) st_q <= ST_POFF_RSP;
        end
        ST_POFF_RSP: begin
          if (rsp_fire) st_q <= ST_DONE;
        end
        default: begin
        end
      endcase
    end
  end

  wire _unused = ^{fab.rsp_rdata, fab.rsp_code, fab.rsp_id};

endmodule : carbon_fabric_bootmaster
