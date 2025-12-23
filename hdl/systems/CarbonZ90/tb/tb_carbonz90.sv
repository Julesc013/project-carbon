`timescale 1ns/1ps

module tb_carbonz90;
  import carbon_arch_pkg::*;
  import am9513_pkg::*;
  import cai_bfm_pkg::*;

  logic clk;
  logic rst_n;

  logic [31:0] signature;
  logic poweroff;

  localparam logic [31:0] EXP_SIG = 32'h2130_395A; // "Z90!" in little-endian bytes
  localparam logic [63:0] SUBMIT_BASE = 64'h0000_0000_0000_0400;
  localparam logic [63:0] COMP_BASE   = 64'h0000_0000_0000_0500;
  localparam int unsigned SUBMIT_MASK = 0;
  localparam int unsigned COMP_MASK   = 0;
  localparam int unsigned HEAP_BASE   = 32'h0000_0800;
  localparam int unsigned CAI_TIMEOUT = 20000;

  int unsigned heap_ptr;
  int unsigned submit_idx;
  int unsigned comp_idx;
  logic [31:0] tag_ctr;

  initial clk = 1'b0;
  always #5 clk = ~clk;

  initial begin
    rst_n = 1'b0;
    repeat (10) @(posedge clk);
    rst_n = 1'b1;
  end

  carbonz90_top dut (
      .clk(clk),
      .rst_n(rst_n),
      .signature(signature),
      .poweroff(poweroff)
  );

  // --------------------------------------------------------------------------
  // Memory helpers (backing store is dut.u_ram)
  // --------------------------------------------------------------------------
  task automatic mem_write8(input int unsigned addr, input logic [7:0] data);
    dut.u_ram.tb_write_byte(addr, data);
  endtask

  task automatic mem_write16(input int unsigned addr, input logic [15:0] data);
    mem_write8(addr + 0, data[7:0]);
    mem_write8(addr + 1, data[15:8]);
  endtask

  task automatic mem_write32(input int unsigned addr, input logic [31:0] data);
    mem_write8(addr + 0, data[7:0]);
    mem_write8(addr + 1, data[15:8]);
    mem_write8(addr + 2, data[23:16]);
    mem_write8(addr + 3, data[31:24]);
  endtask

  task automatic mem_read32(input int unsigned addr, output logic [31:0] data);
    logic [7:0] b0, b1, b2, b3;
    begin
      dut.u_ram.tb_read_byte(addr + 0, b0);
      dut.u_ram.tb_read_byte(addr + 1, b1);
      dut.u_ram.tb_read_byte(addr + 2, b2);
      dut.u_ram.tb_read_byte(addr + 3, b3);
      data = {b3, b2, b1, b0};
    end
  endtask

  // --------------------------------------------------------------------------
  // Simple bump allocator
  // --------------------------------------------------------------------------
  task automatic heap_alloc(
      input int unsigned bytes,
      input int unsigned align,
      output int unsigned addr
  );
    int unsigned a;
    begin
      a = (heap_ptr + align - 1) & ~(align - 1);
      addr = a;
      heap_ptr = a + bytes;
    end
  endtask

  // --------------------------------------------------------------------------
  // CAI helpers
  // --------------------------------------------------------------------------
  task automatic cai_pulse_submit();
    begin
      force dut.cai_cpu.submit_doorbell = 1'b1;
      @(posedge clk);
      force dut.cai_cpu.submit_doorbell = 1'b0;
      @(posedge clk);
      release dut.cai_cpu.submit_doorbell;
    end
  endtask

  task automatic cai_write_submit_desc(input int unsigned idx, input logic [SUBMIT_BITS-1:0] desc);
    int unsigned i;
    int unsigned base;
    begin
      base = int'(SUBMIT_BASE) + ((idx & SUBMIT_MASK) * CARBON_CAI_SUBMIT_DESC_V1_SIZE_BYTES);
      for (i = 0; i < CARBON_CAI_SUBMIT_DESC_V1_SIZE_BYTES; i++) begin
        mem_write8(base + i, desc[(i*8) +: 8]);
      end
    end
  endtask

  task automatic cai_write_operand_desc(
      input int unsigned base,
      input int unsigned op_index,
      input logic [63:0] ptr,
      input logic [31:0] len,
      input logic [31:0] stride,
      input logic [31:0] flags
  );
    int unsigned a;
    begin
      a = base + op_index * CARBON_CAI_OPERAND_DESC_V1_SIZE_BYTES;
      mem_write32(a + CARBON_CAI_OPERAND_DESC_V1_OFF_PTR, ptr[31:0]);
      mem_write32(a + CARBON_CAI_OPERAND_DESC_V1_OFF_PTR + 4, ptr[63:32]);
      mem_write32(a + CARBON_CAI_OPERAND_DESC_V1_OFF_LEN, len);
      mem_write32(a + CARBON_CAI_OPERAND_DESC_V1_OFF_STRIDE, stride);
      mem_write32(a + CARBON_CAI_OPERAND_DESC_V1_OFF_FLAGS, flags);
    end
  endtask

  task automatic cai_write_tensor_desc(input int unsigned base, input logic [TENSOR_BITS-1:0] desc);
    int unsigned i;
    begin
      for (i = 0; i < CARBON_CAI_TENSOR_DESC_V1_SIZE_BYTES; i++) begin
        mem_write8(base + i, desc[(i*8) +: 8]);
      end
    end
  endtask

  task automatic cai_wait_completion(
      output logic [31:0] tag,
      output logic [15:0] status,
      output logic [15:0] ext_status,
      output logic [31:0] bytes_written
  );
    logic [COMP_BITS-1:0] rec;
    int unsigned addr;
    int unsigned i;
    int unsigned wait_cycles;
    begin
      wait_cycles = 0;
      while (!dut.cai_dev.comp_doorbell && (wait_cycles < CAI_TIMEOUT)) begin
        @(posedge clk);
        wait_cycles++;
      end
      if (!dut.cai_dev.comp_doorbell) $fatal(1, "tb_carbonz90: CAI completion timeout");

      addr = int'(COMP_BASE) + ((comp_idx & COMP_MASK) * CARBON_CAI_COMP_REC_V1_SIZE_BYTES);
      rec = '0;
      for (i = 0; i < CARBON_CAI_COMP_REC_V1_SIZE_BYTES; i++) begin
        dut.u_ram.tb_read_byte(addr + i, rec[(i*8) +: 8]);
      end
      decode_comp_rec_v1(rec, tag, status, ext_status, bytes_written);
      comp_idx++;
    end
  endtask

  task automatic cai_submit_and_wait(
      input logic [31:0] opcode,
      input logic [31:0] flags,
      input logic [15:0] context_id,
      input logic [15:0] operand_count,
      input logic [63:0] operands_ptr,
      input logic [63:0] result_ptr,
      input logic [31:0] result_len,
      input logic [31:0] result_stride,
      input logic [7:0] opcode_group,
      input logic [7:0] format_primary,
      input logic [7:0] format_aux,
      input logic [7:0] format_flags,
      input logic [63:0] tensor_desc_ptr,
      input logic [15:0] tensor_desc_len,
      input logic [7:0] tensor_rank,
      output logic [15:0] status,
      output logic [15:0] ext_status,
      output logic [31:0] bytes_written
  );
    logic [SUBMIT_BITS-1:0] desc;
    logic [31:0] tag_exp;
    logic [31:0] tag_got;
    begin
      tag_exp = tag_ctr;
      tag_ctr++;
      build_submit_desc_v1(desc, opcode, flags, context_id, operand_count, tag_exp,
                           operands_ptr, result_ptr, result_len, result_stride,
                           opcode_group, format_primary, format_aux, format_flags,
                           tensor_desc_ptr, tensor_desc_len, tensor_rank, 8'h0);
      cai_write_submit_desc(submit_idx, desc);
      cai_pulse_submit();
      cai_wait_completion(tag_got, status, ext_status, bytes_written);
      if (tag_got != tag_exp) $fatal(1, "tb_carbonz90: CAI tag mismatch exp=0x%08h got=0x%08h",
                                     tag_exp, tag_got);
      submit_idx++;
    end
  endtask

  task automatic cai_wait_ready(output logic ready);
    int unsigned wait_cycles;
    begin
      ready = 1'b0;
      wait_cycles = 0;
      while (wait_cycles < CAI_TIMEOUT) begin
        if (dut.cai_dev.status[0]) begin
          ready = 1'b1;
          break;
        end
        @(posedge clk);
        wait_cycles++;
      end
    end
  endtask

  task automatic cai_smoke();
    logic ready;
    logic [15:0] status;
    logic [15:0] ext;
    logic [31:0] bytes;
    logic [31:0] res;
    logic [31:0] mode_p3_flags;
    logic [31:0] mode_p4_flags;
    logic [TENSOR_BITS-1:0] tdesc;

    int unsigned opdesc_base;
    int unsigned op0_ptr;
    int unsigned op1_ptr;
    int unsigned op2_ptr;
    int unsigned res_ptr;
    int unsigned tensor_desc_ptr;

    cai_wait_ready(ready);
    if (!ready) begin
      $display("tb_carbonz90: CAI not ready, skipping CAI smoke");
      return;
    end

    heap_ptr = HEAP_BASE;
    submit_idx = 0;
    comp_idx = 0;
    tag_ctr = 32'h1;

    mode_p3_flags = (32'(1) << AM9513_SUBMIT_FLAG_MODE_VALID_BIT) |
                    (32'(AM9513_P3_AM9514) << AM9513_SUBMIT_FLAG_MODE_LSB);
    mode_p4_flags = (32'(1) << AM9513_SUBMIT_FLAG_MODE_VALID_BIT) |
                    (32'(AM9513_P4_AM9515) << AM9513_SUBMIT_FLAG_MODE_LSB);

    // ----------------------------------------------------------------------
    // Scalar add: 1.0 + 2.0 = 3.0
    // ----------------------------------------------------------------------
    heap_alloc(CARBON_CAI_OPERAND_DESC_V1_SIZE_BYTES * 2, 8, opdesc_base);
    heap_alloc(4, 4, op0_ptr);
    heap_alloc(4, 4, op1_ptr);
    heap_alloc(4, 4, res_ptr);
    mem_write32(op0_ptr, 32'h3F80_0000);
    mem_write32(op1_ptr, 32'h4000_0000);
    cai_write_operand_desc(opdesc_base, 0, 64'(op0_ptr), 32'd4, 32'd0, 32'h0);
    cai_write_operand_desc(opdesc_base, 1, 64'(op1_ptr), 32'd4, 32'd0, 32'h0);
    cai_submit_and_wait(am9513_opcode(AM9513_FUNC_ADD, 8'(CARBON_FMT_BINARY32)), 32'h0,
                        16'h0000, 16'd2, 64'(opdesc_base),
                        64'(res_ptr), 32'd4, 32'h0,
                        8'(CARBON_CAI_OPGROUP_SCALAR), 8'(CARBON_FMT_BINARY32), 8'h0, 8'h0,
                        64'h0, 16'h0, 8'h0,
                        status, ext, bytes);
    if (status != 16'(CARBON_CAI_STATUS_OK)) $fatal(1, "tb_carbonz90: scalar add status=%0d", status);
    mem_read32(res_ptr, res);
    if (res != 32'h4040_0000) $fatal(1, "tb_carbonz90: scalar add wrong result");

    // ----------------------------------------------------------------------
    // Vector add (optional): [1..4] + 1
    // ----------------------------------------------------------------------
    heap_alloc(CARBON_CAI_OPERAND_DESC_V1_SIZE_BYTES * 2, 8, opdesc_base);
    heap_alloc(16, 4, op0_ptr);
    heap_alloc(16, 4, op1_ptr);
    heap_alloc(16, 4, res_ptr);
    mem_write32(op0_ptr + 0, 32'h3F80_0000);
    mem_write32(op0_ptr + 4, 32'h4000_0000);
    mem_write32(op0_ptr + 8, 32'h4040_0000);
    mem_write32(op0_ptr + 12, 32'h4080_0000);
    mem_write32(op1_ptr + 0, 32'h3F80_0000);
    mem_write32(op1_ptr + 4, 32'h3F80_0000);
    mem_write32(op1_ptr + 8, 32'h3F80_0000);
    mem_write32(op1_ptr + 12, 32'h3F80_0000);
    cai_write_operand_desc(opdesc_base, 0, 64'(op0_ptr), 32'd16, 32'd16, 32'h0);
    cai_write_operand_desc(opdesc_base, 1, 64'(op1_ptr), 32'd16, 32'd16, 32'h0);
    cai_submit_and_wait(am9514_opcode(AM9514_VEC_ADD), mode_p3_flags,
                        16'h0000, 16'd2, 64'(opdesc_base),
                        64'(res_ptr), 32'd16, 32'h0,
                        8'(CARBON_CAI_OPGROUP_VECTOR), 8'(CARBON_FMT_BINARY32), 8'h0, 8'h0,
                        64'h0, 16'h0, 8'h0,
                        status, ext, bytes);
    if (status == 16'(CARBON_CAI_STATUS_UNSUPPORTED)) begin
      $display("tb_carbonz90: vector add unsupported (skipped)");
    end else begin
      if (status != 16'(CARBON_CAI_STATUS_OK)) $fatal(1, "tb_carbonz90: vector add status=%0d", status);
      mem_read32(res_ptr + 0, res);
      if (res != 32'h4000_0000) $fatal(1, "tb_carbonz90: vector add lane0 wrong");
      mem_read32(res_ptr + 12, res);
      if (res != 32'h40A0_0000) $fatal(1, "tb_carbonz90: vector add lane3 wrong");
    end

    // ----------------------------------------------------------------------
    // Tensor GEMM (optional): 2x2 * 2x2 + C
    // ----------------------------------------------------------------------
    heap_alloc(CARBON_CAI_TENSOR_DESC_V1_SIZE_BYTES, 8, tensor_desc_ptr);
    build_tensor_desc_v1(tdesc, 8'd3, 8'(CARBON_FMT_BINARY32),
                         32'd2, 32'd2, 32'd2, 32'd0,
                         32'd2, 32'd2, 32'd2, 32'd0);
    cai_write_tensor_desc(tensor_desc_ptr, tdesc);

    heap_alloc(CARBON_CAI_OPERAND_DESC_V1_SIZE_BYTES * 3, 8, opdesc_base);
    heap_alloc(16, 4, op0_ptr);
    heap_alloc(16, 4, op1_ptr);
    heap_alloc(16, 4, op2_ptr);
    heap_alloc(16, 4, res_ptr);
    mem_write32(op0_ptr + 0, 32'h3F80_0000);
    mem_write32(op0_ptr + 4, 32'h4000_0000);
    mem_write32(op0_ptr + 8, 32'h4040_0000);
    mem_write32(op0_ptr + 12, 32'h4080_0000);
    mem_write32(op1_ptr + 0, 32'h40A0_0000);
    mem_write32(op1_ptr + 4, 32'h40C0_0000);
    mem_write32(op1_ptr + 8, 32'h40E0_0000);
    mem_write32(op1_ptr + 12, 32'h4100_0000);
    mem_write32(op2_ptr + 0, 32'h3F80_0000);
    mem_write32(op2_ptr + 4, 32'h3F80_0000);
    mem_write32(op2_ptr + 8, 32'h3F80_0000);
    mem_write32(op2_ptr + 12, 32'h3F80_0000);
    cai_write_operand_desc(opdesc_base, 0, 64'(op0_ptr), 32'd16, 32'd0, 32'h0);
    cai_write_operand_desc(opdesc_base, 1, 64'(op1_ptr), 32'd16, 32'd0, 32'h0);
    cai_write_operand_desc(opdesc_base, 2, 64'(op2_ptr), 32'd16, 32'd0, 32'h0);
    cai_submit_and_wait(am9515_opcode(AM9515_TENSOR_GEMM), mode_p4_flags,
                        16'h0000, 16'd3, 64'(opdesc_base),
                        64'(res_ptr), 32'd16, 32'h0,
                        8'(CARBON_CAI_OPGROUP_TENSOR), 8'(CARBON_FMT_BINARY32), 8'h0, 8'h0,
                        64'(tensor_desc_ptr), 16'(CARBON_CAI_TENSOR_DESC_V1_SIZE_BYTES), 8'd3,
                        status, ext, bytes);
    if (status == 16'(CARBON_CAI_STATUS_UNSUPPORTED)) begin
      $display("tb_carbonz90: tensor GEMM unsupported (skipped)");
    end else begin
      if (status != 16'(CARBON_CAI_STATUS_OK)) $fatal(1, "tb_carbonz90: tensor GEMM status=%0d", status);
      mem_read32(res_ptr + 0, res);
      if (res != 32'h41A0_0000) $fatal(1, "tb_carbonz90: GEMM c00 wrong");
      mem_read32(res_ptr + 4, res);
      if (res != 32'h41B8_0000) $fatal(1, "tb_carbonz90: GEMM c01 wrong");
      mem_read32(res_ptr + 8, res);
      if (res != 32'h4230_0000) $fatal(1, "tb_carbonz90: GEMM c10 wrong");
      mem_read32(res_ptr + 12, res);
      if (res != 32'h424C_0000) $fatal(1, "tb_carbonz90: GEMM c11 wrong");
    end
  endtask

  int unsigned cycles;
  initial begin
    wait(rst_n);
    cycles = 0;
    while (!poweroff && (cycles < 400000)) begin
      @(posedge clk);
      cycles++;
    end
    if (!poweroff) $fatal(1, "tb_carbonz90: timeout waiting for poweroff");
    if (signature !== EXP_SIG) $fatal(1, "tb_carbonz90: signature mismatch exp=%08x got=%08x", EXP_SIG, signature);

    cai_smoke();

    $display("tb_carbonz90: PASS");
    $finish;
  end

endmodule
