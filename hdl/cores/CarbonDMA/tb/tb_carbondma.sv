`timescale 1ns/1ps

module tb_carbondma;
  import carbon_arch_pkg::*;
  import carbondma_pkg::*;

  localparam int unsigned MEM_BYTES = 4096;
  localparam int unsigned SUBMIT_BASE = 32'h0000_0100;
  localparam int unsigned COMP_BASE   = 32'h0000_0200;
  localparam int unsigned ENTRY_BASE  = 32'h0000_0300;
  localparam int unsigned SRC_Q_BASE  = 32'h0000_0400;
  localparam int unsigned DST_Q_BASE  = 32'h0000_0440;

  logic clk;
  logic rst_n;

  initial clk = 1'b0;
  always #5 clk = ~clk;

  fabric_if compat_if(.clk(clk), .rst_n(rst_n));
  fabric_if mem_if   (.clk(clk), .rst_n(rst_n));
  csr_if    csr      (.clk(clk), .rst_n(rst_n));
  dbg_if    dbg      (.clk(clk), .rst_n(rst_n));

  csr_bfm bfm (.clk(clk), .rst_n(rst_n), .csr(csr));

  fabric_mem_bfm #(
      .MEM_BYTES(MEM_BYTES),
      .RESP_LATENCY(1),
      .STALL_MASK(0)
  ) u_mem (
      .clk(clk),
      .rst_n(rst_n),
      .bus(mem_if)
  );

  carbondma dut (
      .clk(clk),
      .rst_n(rst_n),
      .compat_if(compat_if),
      .mem_if(mem_if),
      .csr(csr),
      .dbg(dbg)
  );

  logic [3:0] compat_id;

  task automatic reset_dut();
    begin
      rst_n = 1'b0;
      compat_if.req_valid = 1'b0;
      compat_if.req_op    = '0;
      compat_if.req_addr  = '0;
      compat_if.req_wdata = '0;
      compat_if.req_wstrb = '0;
      compat_if.req_size  = 3'(2);
      compat_if.req_attr  = '0;
      compat_if.req_id    = '0;
      compat_if.rsp_ready = 1'b1;

      dbg.halt_req  = 1'b0;
      dbg.run_req   = 1'b0;
      dbg.step_req  = 1'b0;
      dbg.bp_valid  = 1'b0;
      dbg.bp_write  = 1'b0;
      dbg.bp_index  = '0;
      dbg.bp_addr   = '0;
      dbg.bp_kind   = '0;
      dbg.bp_enable = 1'b0;
      dbg.trace_ready = 1'b1;

      compat_id = 4'h0;

      repeat (5) @(posedge clk);
      rst_n = 1'b1;
      repeat (5) @(posedge clk);
    end
  endtask

  task automatic mem_write8(input int unsigned addr, input logic [7:0] data);
    if (addr >= MEM_BYTES) $fatal(1, "mem_write8 OOB addr=0x%0h", addr);
    u_mem.mem[addr] = data;
  endtask

  task automatic mem_write32(input int unsigned addr, input logic [31:0] data);
    mem_write8(addr + 0, data[7:0]);
    mem_write8(addr + 1, data[15:8]);
    mem_write8(addr + 2, data[23:16]);
    mem_write8(addr + 3, data[31:24]);
  endtask

  function automatic logic [31:0] mem_read32(input int unsigned addr);
    logic [31:0] v;
    begin
      v[7:0]   = u_mem.mem[addr + 0];
      v[15:8]  = u_mem.mem[addr + 1];
      v[23:16] = u_mem.mem[addr + 2];
      v[31:24] = u_mem.mem[addr + 3];
      mem_read32 = v;
    end
  endfunction

  task automatic csr_write32(input logic [31:0] addr, input logic [31:0] data);
    logic fault;
    begin
      bfm.csr_write(addr, data, 4'hF, 2'b00, fault);
      if (fault) $fatal(1, "csr write fault addr=0x%08h", addr);
    end
  endtask

  task automatic csr_read32(input logic [31:0] addr, output logic [31:0] data);
    logic fault;
    begin
      bfm.csr_read(addr, 2'b00, data, fault);
      if (fault) $fatal(1, "csr read fault addr=0x%08h", addr);
    end
  endtask

  task automatic compat_write32(
      input logic [31:0] addr,
      input logic [31:0] data,
      input logic [3:0] wstrb
  );
    begin
      compat_if.req_valid = 1'b1;
      compat_if.req_op    = 8'(CARBON_FABRIC_XACT_WRITE);
      compat_if.req_addr  = addr;
      compat_if.req_wdata = data;
      compat_if.req_wstrb = wstrb;
      compat_if.req_size  = 3'(2);
      compat_if.req_attr  = '0;
      compat_if.req_id    = compat_id;
      while (!compat_if.req_ready) @(posedge clk);
      @(posedge clk);
      compat_if.req_valid = 1'b0;

      while (!compat_if.rsp_valid) @(posedge clk);
      if (compat_if.rsp_code != 8'(CARBON_FABRIC_RESP_OK)) begin
        $fatal(1, "compat write rsp_code=%0d addr=0x%08h", compat_if.rsp_code, addr);
      end
      if (compat_if.rsp_id != compat_id) begin
        $fatal(1, "compat write rsp_id mismatch exp=%0d got=%0d", compat_id, compat_if.rsp_id);
      end
      @(posedge clk);
      compat_id = compat_id + 1'b1;
    end
  endtask

  task automatic compat_read32(
      input logic [31:0] addr,
      output logic [31:0] data
  );
    begin
      compat_if.req_valid = 1'b1;
      compat_if.req_op    = 8'(CARBON_FABRIC_XACT_READ);
      compat_if.req_addr  = addr;
      compat_if.req_wdata = '0;
      compat_if.req_wstrb = 4'h0;
      compat_if.req_size  = 3'(2);
      compat_if.req_attr  = '0;
      compat_if.req_id    = compat_id;
      while (!compat_if.req_ready) @(posedge clk);
      @(posedge clk);
      compat_if.req_valid = 1'b0;

      while (!compat_if.rsp_valid) @(posedge clk);
      if (compat_if.rsp_code != 8'(CARBON_FABRIC_RESP_OK)) begin
        $fatal(1, "compat read rsp_code=%0d addr=0x%08h", compat_if.rsp_code, addr);
      end
      if (compat_if.rsp_id != compat_id) begin
        $fatal(1, "compat read rsp_id mismatch exp=%0d got=%0d", compat_id, compat_if.rsp_id);
      end
      data = compat_if.rsp_rdata;
      @(posedge clk);
      compat_id = compat_id + 1'b1;
    end
  endtask

  task automatic poll_done(
      input logic use_csr,
      output logic [31:0] status
  );
    int unsigned i;
    begin
      status = 32'h0;
      for (i = 0; i < 200; i++) begin
        if (use_csr) csr_read32(CARBON_CSR_CARBONDMA_CH_STATUS, status);
        else compat_read32(CARBONDMA_COMPAT_CH_STATUS_OFF, status);
        if (status[CARBONDMA_CH_STATUS_DONE_BIT]) break;
        @(posedge clk);
      end
      if (!status[CARBONDMA_CH_STATUS_DONE_BIT]) $fatal(1, "dma did not complete");
    end
  endtask

  initial begin
    logic [31:0] rdata;
    int unsigned i;

    reset_dut();

    // Initialize memory with a simple pattern.
    for (i = 0; i < 256; i++) begin
      u_mem.mem[i] = i[7:0];
    end

    // ------------------------------------------------------------------
    // CSR copy test (channel 0)
    // ------------------------------------------------------------------
    csr_write32(CARBON_CSR_CARBONDMA_CH_SEL, 32'h0);
    csr_write32(CARBON_CSR_CARBONDMA_CH_SRC_LO, 32'h0000_0020);
    csr_write32(CARBON_CSR_CARBONDMA_CH_SRC_HI, 32'h0);
    csr_write32(CARBON_CSR_CARBONDMA_CH_DST_LO, 32'h0000_0080);
    csr_write32(CARBON_CSR_CARBONDMA_CH_DST_HI, 32'h0);
    csr_write32(CARBON_CSR_CARBONDMA_CH_LEN, 32'd32);
    csr_write32(CARBON_CSR_CARBONDMA_CH_CTRL, (32'(1) << CARBONDMA_CH_CTRL_START_BIT));
    poll_done(1'b1, rdata);

    for (i = 0; i < 32; i++) begin
      if (u_mem.mem[32'h0000_0080 + i] != u_mem.mem[32'h0000_0020 + i]) begin
        $fatal(1, "csr copy mismatch at +%0d", i);
      end
    end

    // ------------------------------------------------------------------
    // CSR fill test (channel 1)
    // ------------------------------------------------------------------
    csr_write32(CARBON_CSR_CARBONDMA_CH_SEL, 32'h1);
    csr_write32(CARBON_CSR_CARBONDMA_CH_DST_LO, 32'h0000_00C0);
    csr_write32(CARBON_CSR_CARBONDMA_CH_DST_HI, 32'h0);
    csr_write32(CARBON_CSR_CARBONDMA_CH_LEN, 32'd16);
    csr_write32(CARBON_CSR_CARBONDMA_CH_FILL, 32'hA5A5_A5A5);
    csr_write32(CARBON_CSR_CARBONDMA_CH_CTRL,
                (32'(1) << CARBONDMA_CH_CTRL_START_BIT) |
                (32'(1) << CARBONDMA_CH_CTRL_FILL_BIT));
    poll_done(1'b1, rdata);
    for (i = 0; i < 16; i++) begin
      if (u_mem.mem[32'h0000_00C0 + i] != 8'hA5) begin
        $fatal(1, "csr fill mismatch at +%0d", i);
      end
    end

    // ------------------------------------------------------------------
    // Compatibility path (channel 2)
    // ------------------------------------------------------------------
    compat_read32(CARBONDMA_COMPAT_ID_OFF, rdata);
    if (rdata[15:0] != 16'h0001) $fatal(1, "compat id mismatch");

    compat_write32(CARBONDMA_COMPAT_CH_SEL_OFF, 32'h2, 4'hF);
    compat_write32(CARBONDMA_COMPAT_CH_SRC_LO_OFF, 32'h0000_0040, 4'hF);
    compat_write32(CARBONDMA_COMPAT_CH_DST_LO_OFF, 32'h0000_00E0, 4'hF);
    compat_write32(CARBONDMA_COMPAT_CH_LEN_OFF, 32'd16, 4'hF);
    compat_write32(CARBONDMA_COMPAT_CH_CTRL_OFF, (32'(1) << CARBONDMA_CH_CTRL_START_BIT), 4'hF);
    poll_done(1'b0, rdata);
    for (i = 0; i < 16; i++) begin
      if (u_mem.mem[32'h0000_00E0 + i] != u_mem.mem[32'h0000_0040 + i]) begin
        $fatal(1, "compat copy mismatch at +%0d", i);
      end
    end

    // ------------------------------------------------------------------
    // Turbo queue test (single descriptor)
    // ------------------------------------------------------------------
    // Build payload entry.
    mem_write32(ENTRY_BASE + CARBONDMA_DESC_V1_OFF_SRC_LO, SRC_Q_BASE);
    mem_write32(ENTRY_BASE + CARBONDMA_DESC_V1_OFF_SRC_HI, 32'h0);
    mem_write32(ENTRY_BASE + CARBONDMA_DESC_V1_OFF_DST_LO, DST_Q_BASE);
    mem_write32(ENTRY_BASE + CARBONDMA_DESC_V1_OFF_DST_HI, 32'h0);
    mem_write32(ENTRY_BASE + CARBONDMA_DESC_V1_OFF_LEN, 32'd16);
    mem_write32(ENTRY_BASE + CARBONDMA_DESC_V1_OFF_FLAGS, 32'h0);
    mem_write32(ENTRY_BASE + CARBONDMA_DESC_V1_OFF_FILL, 32'h0);
    mem_write32(ENTRY_BASE + CARBONDMA_DESC_V1_OFF_ATTR, 32'h0);

    // Prepare source data.
    for (i = 0; i < 16; i++) begin
      u_mem.mem[SRC_Q_BASE + i] = (8'h80 + i[7:0]);
    end

    // Build submit descriptor.
    mem_write32(SUBMIT_BASE + 0, (32'(8) << 16) | 32'(1));
    mem_write32(SUBMIT_BASE + 4, (32'(CARBONDMA_OP_COPY) << 16) | 32'h0);
    mem_write32(SUBMIT_BASE + 8, 32'h0);
    mem_write32(SUBMIT_BASE + 12, 32'hBEEF_1234);
    mem_write32(SUBMIT_BASE + 16, ENTRY_BASE);
    mem_write32(SUBMIT_BASE + 20, 32'h0);
    mem_write32(SUBMIT_BASE + 24, 32'(CARBONDMA_DESC_V1_SIZE_BYTES));
    mem_write32(SUBMIT_BASE + 28, 32'h0);

    csr_write32(CARBON_CSR_CARBONDMA_MODE, 32'h1);
    csr_write32(CARBON_CSR_CARBONDMA_QUEUE_SUBMIT_BASE_LO, SUBMIT_BASE);
    csr_write32(CARBON_CSR_CARBONDMA_QUEUE_SUBMIT_BASE_HI, 32'h0);
    csr_write32(CARBON_CSR_CARBONDMA_QUEUE_SUBMIT_MASK, 32'h0);
    csr_write32(CARBON_CSR_CARBONDMA_QUEUE_COMP_BASE_LO, COMP_BASE);
    csr_write32(CARBON_CSR_CARBONDMA_QUEUE_COMP_BASE_HI, 32'h0);
    csr_write32(CARBON_CSR_CARBONDMA_QUEUE_COMP_MASK, 32'h0);
    csr_write32(CARBON_CSR_CARBONDMA_QUEUE_DOORBELL, 32'd1);

    for (i = 0; i < 200; i++) begin
      csr_read32(CARBON_CSR_CARBONDMA_QUEUE_COMP_DOORBELL, rdata);
      if (rdata[0]) break;
      @(posedge clk);
    end
    if (!rdata[0]) $fatal(1, "queue completion doorbell not set");

    if (mem_read32(COMP_BASE + 0) != 32'hBEEF_1234) $fatal(1, "queue tag mismatch");
    if ((mem_read32(COMP_BASE + 4) & 16'hFFFF) != 16'(CARBONDMA_TURBO_STATUS_OK)) begin
      $fatal(1, "queue status mismatch");
    end
    if (mem_read32(COMP_BASE + 8) != 32'd16) $fatal(1, "queue bytes_written mismatch");

    for (i = 0; i < 16; i++) begin
      if (u_mem.mem[DST_Q_BASE + i] != u_mem.mem[SRC_Q_BASE + i]) begin
        $fatal(1, "queue copy mismatch at +%0d", i);
      end
    end

    $display("tb_carbondma: PASS");
    $finish;
  end

endmodule
