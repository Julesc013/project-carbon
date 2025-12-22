`define CARBON_ENABLE_SVA
`timescale 1ns/1ps

module tb_fabric_contract;
  import carbon_arch_pkg::*;

  localparam int unsigned M = 2;
  localparam int unsigned N = 1;
  localparam int unsigned ADDR_W = 32;
  localparam int unsigned DATA_W = 32;
  localparam int unsigned ID_W   = 4;

  logic clk;
  logic rst_n;

  clock_reset_bfm #(
      .CLK_PERIOD(10ns),
      .RESET_CYCLES(5)
  ) clk_rst (
      .clk(clk),
      .rst_n(rst_n)
  );

  initial begin
    clk_rst.apply_reset();
  end

  fabric_if #(
      .ADDR_W(ADDR_W),
      .DATA_W(DATA_W),
      .ID_W(ID_W)
  ) m_if [M] (
      .clk(clk),
      .rst_n(rst_n)
  );

  fabric_if #(
      .ADDR_W(ADDR_W),
      .DATA_W(DATA_W),
      .ID_W(ID_W)
  ) s_if [N] (
      .clk(clk),
      .rst_n(rst_n)
  );

  fabric_arbiter_mxn #(
      .M(M),
      .N(N),
      .ADDR_W(ADDR_W),
      .DATA_W(DATA_W),
      .ID_W(ID_W),
      .SLAVE_BASE('0),
      .SLAVE_MASK('0)
  ) dut (
      .clk(clk),
      .rst_n(rst_n),
      .masters(m_if),
      .slaves(s_if)
  );

  fabric_mem_bfm #(
      .ADDR_W(ADDR_W),
      .DATA_W(DATA_W),
      .ID_W(ID_W),
      .MEM_BYTES(4096),
      .RESP_LATENCY(1),
      .STALL_MASK(32'h0000_000F)
  ) mem (
      .clk(clk),
      .rst_n(rst_n),
      .bus(s_if[0])
  );

  logic [31:0] sb_mem [0:1023];
  int unsigned i;
  initial begin
    for (i = 0; i < 1024; i++) sb_mem[i] = 32'h0;
  end

  logic [ID_W-1:0] id_ctr [M];
  initial begin
    for (i = 0; i < M; i++) id_ctr[i] = '0;
  end

  task automatic master_init(input int unsigned midx);
    begin
      m_if[midx].req_valid = 1'b0;
      m_if[midx].req_op    = '0;
      m_if[midx].req_addr  = '0;
      m_if[midx].req_wdata = '0;
      m_if[midx].req_wstrb = '0;
      m_if[midx].req_size  = 3'(2); // 4B (implementation-defined encoding)
      m_if[midx].req_attr  = '0;
      m_if[midx].req_id    = '0;
      m_if[midx].rsp_ready = 1'b1;
    end
  endtask

  task automatic do_write(
      input int unsigned midx,
      input logic [ADDR_W-1:0] addr,
      input logic [31:0] data,
      input logic [3:0] wstrb
  );
    logic [31:0] prev;
    logic [31:0] exp;
    begin
      prev = sb_mem[addr[11:2]];
      exp  = prev;
      for (int unsigned b = 0; b < 4; b++) begin
        if (wstrb[b]) exp[(b*8)+:8] = data[(b*8)+:8];
      end
      sb_mem[addr[11:2]] = exp;

      m_if[midx].req_valid = 1'b1;
      m_if[midx].req_op    = 8'(CARBON_FABRIC_XACT_WRITE);
      m_if[midx].req_addr  = addr;
      m_if[midx].req_wdata = data;
      m_if[midx].req_wstrb = wstrb;
      m_if[midx].req_size  = 3'(2);
      m_if[midx].req_attr  = '0;
      m_if[midx].req_id    = id_ctr[midx];
      while (!m_if[midx].req_ready) @(posedge clk);
      @(posedge clk);
      m_if[midx].req_valid = 1'b0;

      while (!m_if[midx].rsp_valid) @(posedge clk);
      if (m_if[midx].rsp_code != 8'(CARBON_FABRIC_RESP_OK)) $fatal(1, "write rsp_code=%0d", m_if[midx].rsp_code);
      if (m_if[midx].rsp_id != id_ctr[midx]) $fatal(1, "write rsp_id mismatch");
      @(posedge clk);
      id_ctr[midx] = id_ctr[midx] + 1'b1;
    end
  endtask

  task automatic do_read(
      input int unsigned midx,
      input logic [ADDR_W-1:0] addr
  );
    logic [31:0] exp;
    begin
      exp = sb_mem[addr[11:2]];
      m_if[midx].req_valid = 1'b1;
      m_if[midx].req_op    = 8'(CARBON_FABRIC_XACT_READ);
      m_if[midx].req_addr  = addr;
      m_if[midx].req_wdata = '0;
      m_if[midx].req_wstrb = 4'h0;
      m_if[midx].req_size  = 3'(2);
      m_if[midx].req_attr  = '0;
      m_if[midx].req_id    = id_ctr[midx];
      while (!m_if[midx].req_ready) @(posedge clk);
      @(posedge clk);
      m_if[midx].req_valid = 1'b0;

      while (!m_if[midx].rsp_valid) @(posedge clk);
      if (m_if[midx].rsp_code != 8'(CARBON_FABRIC_RESP_OK)) $fatal(1, "read rsp_code=%0d", m_if[midx].rsp_code);
      if (m_if[midx].rsp_id != id_ctr[midx]) $fatal(1, "read rsp_id mismatch");
      if (m_if[midx].rsp_rdata !== exp) $fatal(1, "read mismatch exp=%08x got=%08x", exp, m_if[midx].rsp_rdata);
      @(posedge clk);
      id_ctr[midx] = id_ctr[midx] + 1'b1;
    end
  endtask

  function automatic logic [31:0] lfsr_next(input logic [31:0] x);
    lfsr_next = {x[30:0], x[31] ^ x[21] ^ x[1] ^ x[0]};
  endfunction

  task automatic master_thread(input int unsigned midx, input logic [31:0] seed);
    logic [31:0] lfsr;
    int unsigned iter;
    begin
      lfsr = seed;
      for (iter = 0; iter < 100; iter++) begin
        logic do_wr;
        logic [31:0] addr;
        logic [31:0] data;
        logic [3:0]  wstrb;

        lfsr = lfsr_next(lfsr);
        do_wr = lfsr[0];
        addr = {20'h0, lfsr[11:2], 2'b00};
        data = lfsr_next(lfsr);
        wstrb = lfsr[5:2] | 4'h1;

        if (do_wr) begin
          do_write(midx, addr, data, wstrb);
        end else begin
          do_read(midx, addr);
        end
      end
    end
  endtask

  initial begin
    wait(rst_n);
    for (i = 0; i < M; i++) master_init(i);

    fork
      master_thread(0, 32'hACE1_1234);
      master_thread(1, 32'hBEEF_0420);
    join

    $display("tb_fabric_contract: PASS");
    $finish;
  end

endmodule
