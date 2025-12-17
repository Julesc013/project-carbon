// Project Carbon - Systems
// carbon_bootrom: Simple fabric-attached read-only boot ROM.

module carbon_bootrom #(
    parameter logic [31:0] BASE_ADDR = 32'h0000_0000,
    parameter int unsigned ROM_BYTES = 256,
    // Packed little-endian byte image: byte i is INIT_IMAGE[(i*8)+:8]
    parameter logic [ROM_BYTES*8-1:0] INIT_IMAGE = '0,
    parameter int unsigned RESP_LATENCY = 1
) (
    input logic clk,
    input logic rst_n,
    fabric_if.slave bus
);
  import carbon_arch_pkg::*;

  localparam int unsigned FAB_ADDR_W = $bits(bus.req_addr);
  localparam int unsigned FAB_DATA_W = $bits(bus.req_wdata);
  localparam int unsigned FAB_STRB_W = $bits(bus.req_wstrb);
  localparam int unsigned FAB_OP_W   = $bits(bus.req_op);
  localparam int unsigned FAB_ID_W   = $bits(bus.req_id);
  localparam int unsigned FAB_CODE_W = $bits(bus.rsp_code);

  localparam int unsigned BYTES_PER_WORD = (FAB_DATA_W / 8);

  // Single outstanding transaction.
  logic busy_q;
  logic [FAB_ADDR_W-1:0] req_addr_q;
  logic [FAB_OP_W-1:0]   req_op_q;
  logic [FAB_ID_W-1:0]   req_id_q;
  logic [31:0]           delay_q;

  // Response registers.
  logic                rsp_valid_q;
  logic [FAB_DATA_W-1:0] rsp_rdata_q;
  logic [FAB_CODE_W-1:0] rsp_code_q;
  logic [FAB_ID_W-1:0]   rsp_id_q;

  assign bus.req_ready = !busy_q;
  assign bus.rsp_valid = rsp_valid_q;
  assign bus.rsp_rdata = rsp_rdata_q;
  assign bus.rsp_code  = rsp_code_q;
  assign bus.rsp_id    = rsp_id_q;

  wire req_fire = bus.req_valid && bus.req_ready;
  wire rsp_fire = bus.rsp_valid && bus.rsp_ready;

  function automatic logic [FAB_DATA_W-1:0] rom_read_word(input logic [FAB_ADDR_W-1:0] addr);
    logic [FAB_DATA_W-1:0] v;
    int signed a0;
    int signed ai;
    int unsigned b;
    begin
      v  = '0;
      a0 = int'(addr) - int'(BASE_ADDR);
      for (b = 0; b < BYTES_PER_WORD; b++) begin
        ai = a0 + int'(b);
        if ((ai >= 0) && (ai < int'(ROM_BYTES))) begin
          v[(b*8)+:8] = INIT_IMAGE[(ai*8)+:8];
        end
      end
      rom_read_word = v;
    end
  endfunction

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      busy_q      <= 1'b0;
      req_addr_q  <= '0;
      req_op_q    <= '0;
      req_id_q    <= '0;
      delay_q     <= '0;
      rsp_valid_q <= 1'b0;
      rsp_rdata_q <= '0;
      rsp_code_q  <= '0;
      rsp_id_q    <= '0;
    end else begin
      if (rsp_fire) begin
        rsp_valid_q <= 1'b0;
      end

      if (busy_q && !rsp_valid_q) begin
        if (delay_q != 0) begin
          delay_q <= delay_q - 1'b1;
        end else begin
          rsp_valid_q <= 1'b1;
        end
      end

      if (req_fire) begin
        busy_q     <= 1'b1;
        req_addr_q <= bus.req_addr;
        req_op_q   <= bus.req_op;
        req_id_q   <= bus.req_id;
        delay_q    <= RESP_LATENCY;

        rsp_id_q    <= bus.req_id;
        rsp_rdata_q <= '0;
        rsp_code_q  <= FAB_CODE_W'(CARBON_FABRIC_RESP_OK);

        if (bus.req_op == FAB_OP_W'(CARBON_FABRIC_XACT_READ)) begin
          rsp_rdata_q <= rom_read_word(bus.req_addr);
        end else if (bus.req_op == FAB_OP_W'(CARBON_FABRIC_XACT_WRITE)) begin
          rsp_code_q <= FAB_CODE_W'(CARBON_FABRIC_RESP_ACCESS_FAULT);
        end else begin
          rsp_code_q <= FAB_CODE_W'(CARBON_FABRIC_RESP_ACCESS_FAULT);
        end
      end

      if (busy_q && rsp_fire) begin
        busy_q <= 1'b0;
      end
    end
  end

  // Unused signals (keeps linters quiet in some flows)
  wire _unused = ^{req_addr_q, req_op_q, req_id_q, bus.req_wdata, bus.req_wstrb, bus.req_size, bus.req_attr};

endmodule : carbon_bootrom

