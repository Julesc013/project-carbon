// Project Carbon - Simulation BFM
// fabric_mem_bfm: Simple memory slave for fabric_if.

module fabric_mem_bfm #(
    parameter int unsigned ADDR_W = 32,
    parameter int unsigned DATA_W = 32,
    parameter int unsigned ID_W   = 4,
    parameter int unsigned OP_W   = 8,
    parameter int unsigned SIZE_W = 3,
    parameter int unsigned ATTR_W = carbon_arch_pkg::CARBON_FABRIC_ATTR_WIDTH_BITS,
    parameter int unsigned CODE_W = 8,

    parameter int unsigned MEM_BYTES = 4096,
    parameter int unsigned RESP_LATENCY = 1,
    parameter int unsigned STALL_MASK = 0,
    parameter string INIT_FILE = "",
    parameter bit INIT_FILE_IS_HEX = 1'b1
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
    ).slave bus
);
  import carbon_arch_pkg::*;

  localparam int unsigned BYTES_PER_WORD = DATA_W / 8;

  logic [7:0] mem [MEM_BYTES];

  logic [31:0] lfsr_q;
  logic [31:0] stall_mask_q;
  logic        stall_enable_q;
  wire stall_now = stall_enable_q && (stall_mask_q != 0) && ((lfsr_q & stall_mask_q) == 0);

  // Single outstanding transaction.
  logic                busy_q;
  logic [ADDR_W-1:0]   req_addr_q;
  logic [DATA_W-1:0]   req_wdata_q;
  logic [BYTES_PER_WORD-1:0] req_wstrb_q;
  logic [OP_W-1:0]     req_op_q;
  logic [ID_W-1:0]     req_id_q;
  logic [31:0]         delay_q;

  // Response registers
  logic               rsp_valid_q;
  logic [DATA_W-1:0]  rsp_rdata_q;
  logic [CODE_W-1:0]  rsp_code_q;
  logic [ID_W-1:0]    rsp_id_q;

  assign bus.req_ready = !busy_q && !stall_now;

  assign bus.rsp_valid = rsp_valid_q;
  assign bus.rsp_rdata = rsp_rdata_q;
  assign bus.rsp_code  = rsp_code_q;
  assign bus.rsp_id    = rsp_id_q;

  wire req_fire = bus.req_valid && bus.req_ready;
  wire rsp_fire = bus.rsp_valid && bus.rsp_ready;

  function automatic logic [DATA_W-1:0] mem_read_word(input logic [ADDR_W-1:0] addr);
    logic [DATA_W-1:0] v;
    int unsigned b;
    int unsigned a;
    begin
      v = '0;
      a = int'(addr);
      for (b = 0; b < BYTES_PER_WORD; b++) begin
        if ((a + b) < MEM_BYTES) begin
          v[(b*8)+:8] = mem[a + b];
        end
      end
      mem_read_word = v;
    end
  endfunction

  task automatic mem_write_word(
      input logic [ADDR_W-1:0] addr,
      input logic [DATA_W-1:0] data,
      input logic [BYTES_PER_WORD-1:0] wstrb
  );
    int unsigned b;
    int unsigned a;
    begin
      a = int'(addr);
      for (b = 0; b < BYTES_PER_WORD; b++) begin
        if (wstrb[b] && ((a + b) < MEM_BYTES)) begin
          mem[a + b] = data[(b*8)+:8];
        end
      end
    end
  endtask

`ifndef SYNTHESIS
  task automatic mem_write8(input int unsigned addr, input logic [7:0] data);
    if (addr < MEM_BYTES) begin
      mem[addr] = data;
    end
  endtask

  function automatic logic [7:0] mem_read8(input int unsigned addr);
    if (addr < MEM_BYTES) mem_read8 = mem[addr];
    else mem_read8 = 8'h00;
  endfunction

  task automatic mem_load_hex(input string path);
    $readmemh(path, mem);
  endtask

  task automatic mem_load_bin(input string path);
    $readmemb(path, mem);
  endtask

  task automatic set_stall_seed(input logic [31:0] seed);
    lfsr_q = seed;
  endtask

  task automatic set_stall_mask(input logic [31:0] mask);
    stall_mask_q = mask;
  endtask

  task automatic set_stall_enable(input logic enable);
    stall_enable_q = enable;
  endtask

  integer init_i;
  initial begin
    for (init_i = 0; init_i < MEM_BYTES; init_i++) begin
      mem[init_i] = 8'h00;
    end
    if (INIT_FILE != "") begin
      if (INIT_FILE_IS_HEX) $readmemh(INIT_FILE, mem);
      else $readmemb(INIT_FILE, mem);
    end
  end
`endif

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      lfsr_q      <= 32'h1;
      stall_mask_q <= STALL_MASK;
      stall_enable_q <= 1'b1;
      busy_q      <= 1'b0;
      delay_q     <= '0;
      rsp_valid_q <= 1'b0;
      rsp_rdata_q <= '0;
      rsp_code_q  <= '0;
      rsp_id_q    <= '0;
    end else begin
      // LFSR (x^32 + x^22 + x^2 + x + 1)
      lfsr_q <= {lfsr_q[30:0], lfsr_q[31] ^ lfsr_q[21] ^ lfsr_q[1] ^ lfsr_q[0]};

      if (rsp_fire) begin
        rsp_valid_q <= 1'b0;
      end

      if (busy_q) begin
        if (!rsp_valid_q) begin
          if (delay_q != 0) begin
            delay_q <= delay_q - 1'b1;
          end else begin
            rsp_valid_q <= 1'b1;
          end
        end
      end

      if (req_fire) begin
        busy_q      <= 1'b1;
        req_addr_q  <= bus.req_addr;
        req_wdata_q <= bus.req_wdata;
        req_wstrb_q <= bus.req_wstrb;
        req_op_q    <= bus.req_op;
        req_id_q    <= bus.req_id;
        delay_q     <= RESP_LATENCY;

        rsp_id_q    <= bus.req_id;
        rsp_rdata_q <= '0;
        rsp_code_q  <= CODE_W'(CARBON_FABRIC_RESP_OK);

        // Bounds check by transaction type.
        if (bus.req_op == OP_W'(CARBON_FABRIC_XACT_ATOMIC)) begin
          if (int'(bus.req_addr) + 2 > MEM_BYTES) begin
            rsp_code_q <= CODE_W'(CARBON_FABRIC_RESP_DECODE_ERR);
          end else begin
            // ATOMIC (v1 scaffolding): CAS16
            logic [15:0] expected;
            logic [15:0] desired;
            logic [15:0] oldv;
            logic success;
            int unsigned a;
            a = int'(bus.req_addr);

            expected = bus.req_wdata[15:0];
            desired  = bus.req_wdata[31:16];
            oldv     = {mem[a + 1], mem[a]};
            success  = (oldv == expected);

            if (success) begin
              mem[a]     = desired[7:0];
              mem[a + 1] = desired[15:8];
            end

            rsp_rdata_q <= '0;
            rsp_rdata_q[15:0] <= oldv;
            if (DATA_W >= 32) begin
              rsp_rdata_q[31] <= success;
            end
          end
        end else if (int'(bus.req_addr) + BYTES_PER_WORD > MEM_BYTES) begin
          rsp_code_q <= CODE_W'(CARBON_FABRIC_RESP_DECODE_ERR);
        end else if (bus.req_op == OP_W'(CARBON_FABRIC_XACT_WRITE)) begin
          mem_write_word(bus.req_addr, bus.req_wdata, bus.req_wstrb);
        end else if (bus.req_op == OP_W'(CARBON_FABRIC_XACT_READ)) begin
          rsp_rdata_q <= mem_read_word(bus.req_addr);
        end else begin
          rsp_code_q <= CODE_W'(CARBON_FABRIC_RESP_ACCESS_FAULT);
        end
      end

      // Clear busy when response is accepted.
      if (busy_q && rsp_fire) begin
        busy_q <= 1'b0;
      end
    end
  end

endmodule : fabric_mem_bfm
