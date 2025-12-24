`timescale 1ns/1ps

module tb_cai_contract;
  import carbon_arch_pkg::*;
  import cai_bfm_pkg::*;

  localparam int unsigned MEM_BYTES = 16384;
  localparam int unsigned SUBMIT_ENTRIES = 4;
  localparam int unsigned COMP_ENTRIES   = 4;

  localparam logic [63:0] SUBMIT_BASE = 64'h0000_0000_0000_0100;
  localparam logic [63:0] COMP_BASE   = 64'h0000_0000_0000_0400;

  localparam logic [31:0] OPC_SCALAR = 32'h8000_0001;
  localparam logic [31:0] OPC_VECTOR = 32'h8000_0002;
  localparam logic [31:0] OPC_TENSOR = 32'h8000_0003;

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

  fabric_if mem_if(.clk(clk), .rst_n(rst_n));
  cai_if    cai   (.clk(clk), .rst_n(rst_n));

  fabric_mem_bfm #(
      .MEM_BYTES(MEM_BYTES),
      .RESP_LATENCY(1),
      .STALL_MASK(0)
  ) u_mem (
      .clk(clk),
      .rst_n(rst_n),
      .bus(mem_if)
  );

  int unsigned submit_head;
  int unsigned comp_head;

  function automatic int unsigned ring_next(input int unsigned idx, input int unsigned size);
    if (size == 0) ring_next = idx;
    else if ((idx + 1) >= size) ring_next = 0;
    else ring_next = idx + 1;
  endfunction

  task automatic read_submit_desc(
      input int unsigned idx,
      output logic [SUBMIT_BITS-1:0] desc
  );
    int unsigned i;
    int unsigned addr;
    begin
      desc = '0;
      addr = int'(SUBMIT_BASE) + (idx * CARBON_CAI_SUBMIT_DESC_V1_SIZE_BYTES);
      for (i = 0; i < CARBON_CAI_SUBMIT_DESC_V1_SIZE_BYTES; i++) begin
        if ((addr + i) < MEM_BYTES) begin
          desc[(i*8) +: 8] = u_mem.mem[addr + i];
        end
      end
    end
  endtask

  task automatic write_comp_rec(
      input int unsigned idx,
      input logic [31:0] tag,
      input logic [15:0] status,
      input logic [15:0] ext_status,
      input logic [31:0] bytes_written
  );
    logic [COMP_BITS-1:0] rec;
    int unsigned addr;
    int unsigned i;
    begin
      rec = '0;
      rec[(CARBON_CAI_COMP_REC_V1_OFF_TAG*8) +: 32] = tag;
      rec[(CARBON_CAI_COMP_REC_V1_OFF_STATUS*8) +: 16] = status;
      rec[(CARBON_CAI_COMP_REC_V1_OFF_EXT_STATUS*8) +: 16] = ext_status;
      rec[(CARBON_CAI_COMP_REC_V1_OFF_BYTES_WRITTEN*8) +: 32] = bytes_written;
      addr = int'(COMP_BASE) + (idx * CARBON_CAI_COMP_REC_V1_SIZE_BYTES);
      for (i = 0; i < CARBON_CAI_COMP_REC_V1_SIZE_BYTES; i++) begin
        if ((addr + i) < MEM_BYTES) begin
          u_mem.mem[addr + i] = rec[(i*8) +: 8];
        end
      end
    end
  endtask

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      submit_head      <= 0;
      comp_head        <= 0;
      cai.comp_base    <= COMP_BASE;
      cai.comp_size    <= 32'(COMP_ENTRIES);
      cai.cai_version  <= 16'(CARBON_CAI_SUBMIT_DESC_V1_VERSION);
      cai.cai_feature_bits <= 32'h0;
      cai.comp_msg     <= 1'b0;
      cai.comp_irq     <= 1'b0;
      cai.status       <= 32'h0;
    end else begin
      cai.comp_msg <= 1'b0;
      if (cai.submit_doorbell) begin
        logic [SUBMIT_BITS-1:0] desc;
        logic ok;
        logic [7:0] opcode_group;
        logic [31:0] tag;
        logic [31:0] result_len;
        logic [15:0] status;
        int unsigned submit_entries;
        int unsigned comp_entries;

        submit_entries = (cai.submit_size == 0) ? 1 : int'(cai.submit_size);
        comp_entries   = (cai.comp_size == 0) ? 1 : int'(cai.comp_size);

        read_submit_desc(submit_head, desc);
        check_submit_desc_v1(desc, ok);
        opcode_group = desc[(CARBON_CAI_SUBMIT_DESC_V1_OFF_OPCODE_GROUP*8) +: 8];
        tag = desc[(CARBON_CAI_SUBMIT_DESC_V1_OFF_TAG*8) +: 32];
        result_len = desc[(CARBON_CAI_SUBMIT_DESC_V1_OFF_RESULT_LEN*8) +: 32];

        if (!ok) begin
          status = 16'(CARBON_CAI_STATUS_INVALID_OP);
        end else if ((opcode_group == 8'(CARBON_AM95_SCALAR)) ||
                     (opcode_group == 8'(CARBON_AM95_VECTOR)) ||
                     (opcode_group == 8'(CARBON_AM95_TENSOR))) begin
          status = 16'(CARBON_CAI_STATUS_OK);
        end else begin
          status = 16'(CARBON_CAI_STATUS_UNSUPPORTED);
        end

        write_comp_rec(comp_head, tag, status, 16'h0000,
                       (status == 16'(CARBON_CAI_STATUS_OK)) ? result_len : 32'h0);
        cai.comp_msg <= 1'b1;

        submit_head <= ring_next(submit_head, submit_entries);
        comp_head   <= ring_next(comp_head, comp_entries);
      end
    end
  end

  initial begin
    logic [SUBMIT_BITS-1:0] desc;
    logic [COMP_BITS-1:0] comp;
    logic [31:0] tag;
    logic [15:0] status;
    logic [15:0] ext_status;
    logic [31:0] bytes_written;
    logic ok;
    int unsigned comp_idx;

    wait (rst_n);

    cai.submit_base = SUBMIT_BASE;
    cai.submit_size = 32'(SUBMIT_ENTRIES);
    cai.submit_doorbell = 1'b0;
    cai.context_sel = 16'h0000;

    comp_idx = 0;

    build_submit_desc_v1(desc,
                         OPC_SCALAR,
                         32'h0,
                         16'h0000,
                         16'd0,
                         32'h1111_0001,
                         64'h0,
                         64'h0,
                         32'd16,
                         32'h0,
                         8'(CARBON_AM95_SCALAR),
                         8'h00,
                         8'h00,
                         8'h00);
    write_submit_desc_v1(u_mem.mem, SUBMIT_BASE, 0, desc);
    cai_fence(cai);
    cai_ring_submit(cai);
    cai_wait_comp_msg(cai);
    read_comp_rec_v1(u_mem.mem, COMP_BASE, comp_idx, comp);
    check_comp_rec_v1(comp, ok);
    if (!ok) $fatal(1, "comp reserved bits nonzero (scalar)");
    decode_comp_rec_v1(comp, tag, status, ext_status, bytes_written);
    if (tag != 32'h1111_0001) $fatal(1, "scalar tag mismatch");
    if (status != 16'(CARBON_CAI_STATUS_OK)) $fatal(1, "scalar status=%0d", status);
    if (bytes_written != 32'd16) $fatal(1, "scalar bytes_written=%0d", bytes_written);
    cai_fence(cai);
    comp_idx++;

    build_submit_desc_v1(desc,
                         OPC_VECTOR,
                         32'h0,
                         16'h0000,
                         16'd0,
                         32'h2222_0002,
                         64'h0,
                         64'h0,
                         32'd32,
                         32'h0,
                         8'(CARBON_AM95_VECTOR),
                         8'h00,
                         8'h00,
                         8'h00);
    write_submit_desc_v1(u_mem.mem, SUBMIT_BASE, 1, desc);
    cai_fence(cai);
    cai_ring_submit(cai);
    cai_wait_comp_msg(cai);
    read_comp_rec_v1(u_mem.mem, COMP_BASE, comp_idx, comp);
    check_comp_rec_v1(comp, ok);
    if (!ok) $fatal(1, "comp reserved bits nonzero (vector)");
    decode_comp_rec_v1(comp, tag, status, ext_status, bytes_written);
    if (tag != 32'h2222_0002) $fatal(1, "vector tag mismatch");
    if (status != 16'(CARBON_CAI_STATUS_OK)) $fatal(1, "vector status=%0d", status);
    if (bytes_written != 32'd32) $fatal(1, "vector bytes_written=%0d", bytes_written);
    cai_fence(cai);
    comp_idx++;

    build_submit_desc_v1(desc,
                         OPC_TENSOR,
                         32'h0,
                         16'h0000,
                         16'd0,
                         32'h3333_0003,
                         64'h0,
                         64'h0,
                         32'd64,
                         32'h0,
                         8'(CARBON_AM95_TENSOR),
                         8'h00,
                         8'h00,
                         8'h00);
    write_submit_desc_v1(u_mem.mem, SUBMIT_BASE, 2, desc);
    cai_fence(cai);
    cai_ring_submit(cai);
    cai_wait_comp_msg(cai);
    read_comp_rec_v1(u_mem.mem, COMP_BASE, comp_idx, comp);
    check_comp_rec_v1(comp, ok);
    if (!ok) $fatal(1, "comp reserved bits nonzero (tensor)");
    decode_comp_rec_v1(comp, tag, status, ext_status, bytes_written);
    if (tag != 32'h3333_0003) $fatal(1, "tensor tag mismatch");
    if (status != 16'(CARBON_CAI_STATUS_OK)) $fatal(1, "tensor status=%0d", status);
    if (bytes_written != 32'd64) $fatal(1, "tensor bytes_written=%0d", bytes_written);
    cai_fence(cai);
    comp_idx++;

    build_submit_desc_v1(desc,
                         OPC_SCALAR,
                         32'h0,
                         16'h0000,
                         16'd0,
                         32'h4444_0004,
                         64'h0,
                         64'h0,
                         32'd8,
                         32'h0,
                         8'(CARBON_AM95_SCALAR),
                         8'h00,
                         8'h00,
                         8'h00);
    desc[(CARBON_CAI_SUBMIT_DESC_V1_OFF_DESC_VERSION*8) +: 16] = 16'(CARBON_CAI_SUBMIT_DESC_V1_VERSION + 1);
    write_submit_desc_v1(u_mem.mem, SUBMIT_BASE, 3, desc);
    cai_fence(cai);
    cai_ring_submit(cai);
    cai_wait_comp_msg(cai);
    read_comp_rec_v1(u_mem.mem, COMP_BASE, comp_idx, comp);
    check_comp_rec_v1(comp, ok);
    if (!ok) $fatal(1, "comp reserved bits nonzero (invalid)");
    decode_comp_rec_v1(comp, tag, status, ext_status, bytes_written);
    if (tag != 32'h4444_0004) $fatal(1, "invalid tag mismatch");
    if (status != 16'(CARBON_CAI_STATUS_INVALID_OP)) $fatal(1, "invalid status=%0d", status);
    if (bytes_written != 32'd0) $fatal(1, "invalid bytes_written=%0d", bytes_written);
    cai_fence(cai);

    $display("tb_cai_contract: PASS");
    $finish;
  end

endmodule
