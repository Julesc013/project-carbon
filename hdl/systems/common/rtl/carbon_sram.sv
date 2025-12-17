// Project Carbon - Systems
// carbon_sram: Simple synthesizable on-fabric SRAM with byte strobes.

module carbon_sram #(
    parameter logic [31:0] BASE_ADDR = 32'h0000_0000,
    parameter int unsigned MEM_BYTES = 65536,
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

  // Byte-addressed memory.
  logic [7:0] mem [MEM_BYTES];

`ifndef SYNTHESIS
  integer init_i;
  initial begin
    for (init_i = 0; init_i < int'(MEM_BYTES); init_i++) begin
      mem[init_i] = 8'h00;
    end
  end

  task automatic tb_write_byte(input int unsigned addr, input logic [7:0] data);
    if (addr < MEM_BYTES) mem[addr] = data;
  endtask

  task automatic tb_read_byte(input int unsigned addr, output logic [7:0] data);
    data = (addr < MEM_BYTES) ? mem[addr] : 8'h00;
  endtask
`endif

  // Single outstanding transaction.
  logic busy_q;
  logic [31:0] delay_q;

  // Response registers.
  logic                 rsp_valid_q;
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

  function automatic logic [FAB_DATA_W-1:0] mem_read_word(input logic [FAB_ADDR_W-1:0] addr);
    logic [FAB_DATA_W-1:0] v;
    int signed a0;
    int signed ai;
    int unsigned b;
    begin
      v  = '0;
      a0 = int'(addr) - int'(BASE_ADDR);
      for (b = 0; b < BYTES_PER_WORD; b++) begin
        ai = a0 + int'(b);
        if ((ai >= 0) && (ai < int'(MEM_BYTES))) begin
          v[(b*8)+:8] = mem[ai];
        end
      end
      mem_read_word = v;
    end
  endfunction

  task automatic mem_write_word(
      input logic [FAB_ADDR_W-1:0] addr,
      input logic [FAB_DATA_W-1:0] data,
      input logic [FAB_STRB_W-1:0] wstrb
  );
    int signed a0;
    int signed ai;
    int unsigned b;
    begin
      a0 = int'(addr) - int'(BASE_ADDR);
      for (b = 0; b < BYTES_PER_WORD; b++) begin
        ai = a0 + int'(b);
        if (wstrb[b] && (ai >= 0) && (ai < int'(MEM_BYTES))) begin
          mem[ai] = data[(b*8)+:8];
        end
      end
    end
  endtask

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      busy_q      <= 1'b0;
      delay_q     <= '0;
      rsp_valid_q <= 1'b0;
      rsp_rdata_q <= '0;
      rsp_code_q  <= '0;
      rsp_id_q    <= '0;
    end else begin
      if (rsp_fire) rsp_valid_q <= 1'b0;

      if (busy_q && !rsp_valid_q) begin
        if (delay_q != 0) begin
          delay_q <= delay_q - 1'b1;
        end else begin
          rsp_valid_q <= 1'b1;
        end
      end

      if (req_fire) begin
        int signed a0;
        a0 = int'(bus.req_addr) - int'(BASE_ADDR);

        busy_q   <= 1'b1;
        delay_q  <= RESP_LATENCY;
        rsp_id_q <= bus.req_id;

        rsp_rdata_q <= '0;
        rsp_code_q  <= FAB_CODE_W'(CARBON_FABRIC_RESP_OK);

        // Bounds check by transaction type.
        if ((a0 < 0) || (a0 >= int'(MEM_BYTES))) begin
          rsp_code_q <= FAB_CODE_W'(CARBON_FABRIC_RESP_DECODE_ERR);
        end else if (bus.req_op == FAB_OP_W'(CARBON_FABRIC_XACT_ATOMIC)) begin
          if (a0 + 2 > int'(MEM_BYTES)) begin
            rsp_code_q <= FAB_CODE_W'(CARBON_FABRIC_RESP_DECODE_ERR);
          end else begin
            // ATOMIC (v1 scaffolding): CAS16 (matches fabric_mem_bfm contract)
            logic [15:0] expected;
            logic [15:0] desired;
            logic [15:0] oldv;
            logic success;

            expected = bus.req_wdata[15:0];
            desired  = bus.req_wdata[31:16];
            oldv     = {mem[a0 + 1], mem[a0]};
            success  = (oldv == expected);

            if (success) begin
              mem[a0]     = desired[7:0];
              mem[a0 + 1] = desired[15:8];
            end

            rsp_rdata_q <= '0;
            rsp_rdata_q[15:0] <= oldv;
            if (FAB_DATA_W >= 32) begin
              rsp_rdata_q[31] <= success;
            end
          end
        end else if (a0 + int'(BYTES_PER_WORD) > int'(MEM_BYTES)) begin
          rsp_code_q <= FAB_CODE_W'(CARBON_FABRIC_RESP_DECODE_ERR);
        end else if (bus.req_op == FAB_OP_W'(CARBON_FABRIC_XACT_WRITE)) begin
          mem_write_word(bus.req_addr, bus.req_wdata, bus.req_wstrb);
        end else if (bus.req_op == FAB_OP_W'(CARBON_FABRIC_XACT_READ)) begin
          rsp_rdata_q <= mem_read_word(bus.req_addr);
        end else begin
          rsp_code_q <= FAB_CODE_W'(CARBON_FABRIC_RESP_ACCESS_FAULT);
        end
      end

      if (busy_q && rsp_fire) begin
        busy_q <= 1'b0;
      end
    end
  end

  wire _unused = ^{bus.req_size, bus.req_attr, bus.req_wstrb};

endmodule : carbon_sram

