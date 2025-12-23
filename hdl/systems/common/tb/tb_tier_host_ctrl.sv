`timescale 1ns/1ps

module tb_tier_host_ctrl;
  import carbon_arch_pkg::*;
  import carbon_memmap_pkg::*;

  logic clk;
  logic rst_n;

  fabric_if bus (
      .clk(clk),
      .rst_n(rst_n)
  );

  localparam logic [CARBON_FABRIC_ATTR_WIDTH_BITS-1:0] ATTR_IO =
      logic [CARBON_FABRIC_ATTR_WIDTH_BITS-1:0]'(
          CARBON_FABRIC_ATTR_IO_SPACE_MASK | CARBON_FABRIC_ATTR_ORDERED_MASK
      );

  tier_host_ctrl #(
      .BASE_ADDR(CARBON_SYS16_TIER_HOST_BASE)
  ) dut (
      .clk(clk),
      .rst_n(rst_n),
      .bus(bus),
      .active_tier(),
      .active_core(),
      .core_halt_req(),
      .core_run_pulse()
  );

  initial clk = 1'b0;
  always #5 clk = ~clk;

  initial begin
    rst_n = 1'b0;
    bus.req_valid = 1'b0;
    bus.req_op = '0;
    bus.req_addr = '0;
    bus.req_wdata = '0;
    bus.req_wstrb = '0;
    bus.req_size = '0;
    bus.req_attr = '0;
    bus.req_id = '0;
    bus.rsp_ready = 1'b1;
    repeat (5) @(posedge clk);
    rst_n = 1'b1;
  end

  task automatic fab_write32(input logic [31:0] addr, input logic [31:0] data);
    begin
      bus.req_valid <= 1'b1;
      bus.req_op    <= CARBON_FABRIC_XACT_WRITE;
      bus.req_addr  <= addr;
      bus.req_wdata <= data;
      bus.req_wstrb <= 4'hF;
      bus.req_size  <= 3'd2;
      bus.req_attr  <= ATTR_IO;
      bus.req_id    <= '0;
      while (!bus.req_ready) @(posedge clk);
      @(posedge clk);
      bus.req_valid <= 1'b0;
      while (!bus.rsp_valid) @(posedge clk);
      if (bus.rsp_code != CARBON_FABRIC_RESP_OK) begin
        $fatal(1, "tb_tier_host_ctrl: write resp code %0d", bus.rsp_code);
      end
      @(posedge clk);
    end
  endtask

  task automatic fab_read32(input logic [31:0] addr, output logic [31:0] data);
    begin
      bus.req_valid <= 1'b1;
      bus.req_op    <= CARBON_FABRIC_XACT_READ;
      bus.req_addr  <= addr;
      bus.req_wdata <= '0;
      bus.req_wstrb <= '0;
      bus.req_size  <= 3'd2;
      bus.req_attr  <= ATTR_IO;
      bus.req_id    <= '0;
      while (!bus.req_ready) @(posedge clk);
      @(posedge clk);
      bus.req_valid <= 1'b0;
      while (!bus.rsp_valid) @(posedge clk);
      if (bus.rsp_code != CARBON_FABRIC_RESP_OK) begin
        $fatal(1, "tb_tier_host_ctrl: read resp code %0d", bus.rsp_code);
      end
      data = bus.rsp_rdata;
      @(posedge clk);
    end
  endtask

  task automatic read_status(
      output logic [7:0] tier,
      output logic [7:0] sp,
      output logic [1:0] core,
      output logic err_invalid,
      output logic err_overflow,
      output logic err_underflow
  );
    logic [31:0] v;
    begin
      fab_read32(CARBON_SYS16_TIER_HOST_BASE + 32'h4, v);
      tier = v[7:0];
      sp = v[15:8];
      core = v[17:16];
      err_invalid = v[24];
      err_overflow = v[25];
      err_underflow = v[26];
    end
  endtask

  initial begin
    logic [7:0] tier;
    logic [7:0] sp;
    logic [1:0] core;
    logic err_invalid;
    logic err_overflow;
    logic err_underflow;

    wait(rst_n);

    read_status(tier, sp, core, err_invalid, err_overflow, err_underflow);
    if (tier != 8'(CARBON_Z80_DERIVED_TIER_P0_I8080)) $fatal(1, "reset tier mismatch");
    if (sp != 8'd0) $fatal(1, "reset mode stack not empty");
    if (core != 2'd0) $fatal(1, "reset core mismatch");

    fab_write32(CARBON_SYS16_TIER_HOST_BASE, 32'(CARBON_Z80_DERIVED_TIER_P2_Z80));
    read_status(tier, sp, core, err_invalid, err_overflow, err_underflow);
    if (tier != 8'(CARBON_Z80_DERIVED_TIER_P2_Z80)) $fatal(1, "modeup P2 tier mismatch");
    if (sp != 8'd1) $fatal(1, "modeup P2 sp mismatch");
    if (core != 2'd0) $fatal(1, "modeup P2 core mismatch");

    fab_write32(CARBON_SYS16_TIER_HOST_BASE, 32'(CARBON_Z80_DERIVED_TIER_P3_Z180));
    read_status(tier, sp, core, err_invalid, err_overflow, err_underflow);
    if (tier != 8'(CARBON_Z80_DERIVED_TIER_P3_Z180)) $fatal(1, "modeup P3 tier mismatch");
    if (sp != 8'd2) $fatal(1, "modeup P3 sp mismatch");
    if (core != 2'd1) $fatal(1, "modeup P3 core mismatch");

    fab_write32(CARBON_SYS16_TIER_HOST_BASE, 32'(CARBON_Z80_DERIVED_TIER_P6_Z380));
    read_status(tier, sp, core, err_invalid, err_overflow, err_underflow);
    if (tier != 8'(CARBON_Z80_DERIVED_TIER_P6_Z380)) $fatal(1, "modeup P6 tier mismatch");
    if (sp != 8'd3) $fatal(1, "modeup P6 sp mismatch");
    if (core != 2'd2) $fatal(1, "modeup P6 core mismatch");

    fab_write32(CARBON_SYS16_TIER_HOST_BASE, 32'(CARBON_Z80_DERIVED_TIER_P7_Z480));
    read_status(tier, sp, core, err_invalid, err_overflow, err_underflow);
    if (tier != 8'(CARBON_Z80_DERIVED_TIER_P7_Z480)) $fatal(1, "modeup P7 tier mismatch");
    if (sp != 8'd4) $fatal(1, "modeup P7 sp mismatch");
    if (core != 2'd3) $fatal(1, "modeup P7 core mismatch");

    fab_write32(CARBON_SYS16_TIER_HOST_BASE, 32'(CARBON_Z80_DERIVED_TIER_P7_Z480));
    read_status(tier, sp, core, err_invalid, err_overflow, err_underflow);
    if (!err_invalid) $fatal(1, "invalid modeup flag not set");
    if (tier != 8'(CARBON_Z80_DERIVED_TIER_P7_Z480)) $fatal(1, "invalid modeup tier changed");

    fab_write32(CARBON_SYS16_TIER_HOST_BASE, 32'h0000_0080);
    read_status(tier, sp, core, err_invalid, err_overflow, err_underflow);
    if (tier != 8'(CARBON_Z80_DERIVED_TIER_P6_Z380)) $fatal(1, "retmd tier mismatch");
    if (sp != 8'd3) $fatal(1, "retmd sp mismatch");
    if (core != 2'd2) $fatal(1, "retmd core mismatch");

    fab_write32(CARBON_SYS16_TIER_HOST_BASE, 32'h0000_0080);
    read_status(tier, sp, core, err_invalid, err_overflow, err_underflow);
    if (tier != 8'(CARBON_Z80_DERIVED_TIER_P3_Z180)) $fatal(1, "retmd tier mismatch (P3)");
    if (sp != 8'd2) $fatal(1, "retmd sp mismatch (P3)");
    if (core != 2'd1) $fatal(1, "retmd core mismatch (P3)");

    fab_write32(CARBON_SYS16_TIER_HOST_BASE, 32'h0000_0080);
    read_status(tier, sp, core, err_invalid, err_overflow, err_underflow);
    if (tier != 8'(CARBON_Z80_DERIVED_TIER_P2_Z80)) $fatal(1, "retmd tier mismatch (P2)");
    if (sp != 8'd1) $fatal(1, "retmd sp mismatch (P2)");
    if (core != 2'd0) $fatal(1, "retmd core mismatch (P2)");

    fab_write32(CARBON_SYS16_TIER_HOST_BASE, 32'h0000_0080);
    read_status(tier, sp, core, err_invalid, err_overflow, err_underflow);
    if (tier != 8'(CARBON_Z80_DERIVED_TIER_P0_I8080)) $fatal(1, "retmd tier mismatch (P0)");
    if (sp != 8'd0) $fatal(1, "retmd sp mismatch (P0)");
    if (core != 2'd0) $fatal(1, "retmd core mismatch (P0)");

    fab_write32(CARBON_SYS16_TIER_HOST_BASE, 32'h0000_0080);
    read_status(tier, sp, core, err_invalid, err_overflow, err_underflow);
    if (!err_underflow) $fatal(1, "underflow flag not set");

    $display("tb_tier_host_ctrl: PASS");
    $finish;
  end

endmodule
