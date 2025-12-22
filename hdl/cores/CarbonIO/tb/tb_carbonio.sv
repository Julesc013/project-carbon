`timescale 1ns/1ps

module tb_carbonio;
  import carbon_arch_pkg::*;
  import carbonio_pkg::*;

  localparam int unsigned PIO_WIDTH = CARBONIO_PIO_WIDTH_DEFAULT;

  logic clk;
  logic rst_n;

  initial clk = 1'b0;
  always #5 clk = ~clk;

  fabric_if compat_if(.clk(clk), .rst_n(rst_n));
  csr_if    csr      (.clk(clk), .rst_n(rst_n));
  dbg_if    dbg      (.clk(clk), .rst_n(rst_n));
  irq_if #(.N(CARBONIO_IRQ_SRC_COUNT)) irq(.clk(clk), .rst_n(rst_n));

  csr_bfm bfm (.clk(clk), .rst_n(rst_n), .csr(csr));

  logic       uart_rx_valid;
  logic [7:0] uart_rx_data;
  logic       uart_rx_ready;
  logic       uart_tx_ready;
  logic       uart_tx_valid;
  logic [7:0] uart_tx_data;

  logic [PIO_WIDTH-1:0] pio_in;
  logic [PIO_WIDTH-1:0] pio_out;
  logic [PIO_WIDTH-1:0] pio_dir;

  carbonio dut (
      .clk(clk),
      .rst_n(rst_n),
      .compat_if(compat_if),
      .csr(csr),
      .dbg(dbg),
      .irq(irq),
      .uart_rx_valid(uart_rx_valid),
      .uart_rx_data(uart_rx_data),
      .uart_rx_ready(uart_rx_ready),
      .uart_tx_ready(uart_tx_ready),
      .uart_tx_valid(uart_tx_valid),
      .uart_tx_data(uart_tx_data),
      .pio_in(pio_in),
      .pio_out(pio_out),
      .pio_dir(pio_dir)
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
      compat_if.req_size  = 3'(2); // 4B
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

      irq.irq_ack = 1'b0;
      irq.irq_ack_vector = '0;

      uart_rx_valid = 1'b0;
      uart_rx_data  = 8'h0;
      uart_tx_ready = 1'b1;

      pio_in = '0;
      compat_id = 4'h0;

      repeat (5) @(posedge clk);
      rst_n = 1'b1;
      repeat (5) @(posedge clk);
    end
  endtask

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

  task automatic uart_push_byte(input logic [7:0] data);
    begin
      uart_rx_data <= data;
      uart_rx_valid <= 1'b1;
      while (!uart_rx_ready) @(posedge clk);
      @(posedge clk);
      uart_rx_valid <= 1'b0;
    end
  endtask

  task automatic uart_expect_tx(input logic [7:0] exp);
    begin
      while (!uart_tx_valid) @(posedge clk);
      if (uart_tx_data !== exp) $fatal(1, "uart tx mismatch exp=%02h got=%02h", exp, uart_tx_data);
      @(posedge clk);
    end
  endtask

  initial begin
    logic [31:0] rdata0;
    logic [31:0] rdata1;

    reset_dut();

    // CSR: ID register is stable.
    csr_read32(CARBON_CSR_CARBONIO_ID, rdata0);
    if (rdata0[15:0] != 16'h0001) $fatal(1, "carbonio id mismatch");

    // Tick should increment.
    csr_read32(CARBON_CSR_CARBONIO_TICK_LO, rdata0);
    repeat (10) @(posedge clk);
    csr_read32(CARBON_CSR_CARBONIO_TICK_LO, rdata1);
    if (rdata1 <= rdata0) $fatal(1, "tick did not increment");

    // UART RX FIFO path.
    uart_push_byte(8'h11);
    uart_push_byte(8'h22);
    csr_read32(CARBON_CSR_CARBONIO_UART_RX_COUNT, rdata0);
    if (rdata0 != 32'd2) $fatal(1, "uart rx_count mismatch exp=2 got=%0d", rdata0);
    csr_read32(CARBON_CSR_CARBONIO_UART_RX_RDATA, rdata0);
    if (rdata0[7:0] != 8'h11) $fatal(1, "uart rx data mismatch");
    csr_read32(CARBON_CSR_CARBONIO_UART_RX_RDATA, rdata0);
    if (rdata0[7:0] != 8'h22) $fatal(1, "uart rx data mismatch");
    csr_read32(CARBON_CSR_CARBONIO_UART_RX_COUNT, rdata0);
    if (rdata0 != 32'd0) $fatal(1, "uart rx_count not empty");

    // UART TX FIFO path.
    csr_write32(CARBON_CSR_CARBONIO_UART_TX_WDATA, 32'h0000_00A5);
    uart_expect_tx(8'hA5);
    csr_write32(CARBON_CSR_CARBONIO_UART_TX_WDATA, 32'h0000_005A);
    uart_expect_tx(8'h5A);

    // PIO edge capture.
    pio_in <= '0;
    @(posedge clk);
    pio_in <= 32'h0000_0001;
    repeat (3) @(posedge clk);
    csr_read32(CARBON_CSR_CARBONIO_PIO_EDGE_COUNT, rdata0);
    if (rdata0 != 32'd1) $fatal(1, "pio edge_count mismatch exp=1 got=%0d", rdata0);
    csr_read32(CARBON_CSR_CARBONIO_PIO_EDGE_RDATA, rdata0);
    if (rdata0[0] != 1'b1) $fatal(1, "pio edge data mismatch");
    csr_read32(CARBON_CSR_CARBONIO_PIO_EDGE_COUNT, rdata0);
    if (rdata0 != 32'd0) $fatal(1, "pio edge_count not empty");

    // Timer polling completion.
    csr_write32(CARBON_CSR_CARBONIO_TIMER0_LOAD, 32'd5);
    csr_write32(CARBON_CSR_CARBONIO_TIMER0_CTRL, 32'h0000_0005); // enable + load
    repeat (20) begin
      csr_read32(CARBON_CSR_CARBONIO_TIMER0_STATUS, rdata0);
      if (rdata0[0]) break;
      @(posedge clk);
    end
    if (!rdata0[0]) $fatal(1, "timer0 did not expire");
    csr_write32(CARBON_CSR_CARBONIO_TIMER0_STATUS, 32'h1);
    csr_read32(CARBON_CSR_CARBONIO_TIMER0_STATUS, rdata0);
    if (rdata0[0]) $fatal(1, "timer0 status did not clear");

    // Compatibility window reads/writes.
    compat_write32(CARBONIO_COMPAT_UART_WATERMARKS_OFF, 32'h0002_0003, 4'hF);
    compat_read32(CARBONIO_COMPAT_UART_WATERMARKS_OFF, rdata0);
    if (rdata0 != 32'h0002_0003) $fatal(1, "compat uart watermark mismatch");
    compat_write32(CARBONIO_COMPAT_IRQ_ENABLE_OFF, 32'h0000_003F, 4'hF);
    compat_read32(CARBONIO_COMPAT_IRQ_ENABLE_OFF, rdata0);
    if (rdata0[5:0] != 6'h3F) $fatal(1, "compat irq_enable mismatch");
    compat_write32(CARBONIO_COMPAT_IRQ_MASK_OFF, 32'h0000_0001, 4'hF);
    compat_read32(CARBONIO_COMPAT_IRQ_MASK_OFF, rdata0);
    if (rdata0[0] != 1'b1) $fatal(1, "compat irq_mask mismatch");

    $display("tb_carbonio: PASS");
    $finish;
  end

endmodule
