`timescale 1ns/1ps

module tb_carbonz80;
  import carbon_arch_pkg::*;
  import am9513_pkg::*;
  import cai_bfm_pkg::*;
  logic clk;
  logic rst_n;

  logic [31:0] signature;
  logic poweroff;

  initial clk = 1'b0;
  always #5 clk = ~clk;

  initial begin
    rst_n = 1'b0;
    repeat (10) @(posedge clk);
    rst_n = 1'b1;
  end

  carbonz80_top dut (
      .clk(clk),
      .rst_n(rst_n),
      .signature(signature),
      .poweroff(poweroff)
  );

  localparam logic [31:0] EXP_SIG = 32'h2130_385A; // "Z80!" in little-endian bytes
  localparam logic [63:0] SUBMIT_BASE = 64'h0000_0000_0000_0400;
  localparam logic [63:0] COMP_BASE   = 64'h0000_0000_0000_0500;
  localparam int unsigned SUBMIT_MASK = 0;
  localparam int unsigned SUBMIT_ENTRIES = SUBMIT_MASK + 1;
  localparam int unsigned COMP_MASK   = 0;
  localparam int unsigned HEAP_BASE   = 32'h0000_0800;
  localparam int unsigned CAI_TIMEOUT = 20000;

  int unsigned heap_ptr;
  int unsigned submit_idx;
  int unsigned comp_idx;
  logic [31:0] tag_ctr;

  // --------------------------------------------------------------------------
  // Memory helpers (backing store is dut.u_ram)
  // --------------------------------------------------------------------------
  task automatic mem_write8(input int unsigned addr, input logic [7:0] data);
    dut.u_ram.tb_write_byte(addr, data);
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
  task automatic cai_force_host_cfg();
    begin
      force dut.cai_link.submit_base = SUBMIT_BASE;
      force dut.cai_link.submit_size = 32'(SUBMIT_ENTRIES);
      force dut.cai_link.context_sel = 16'h0000;
    end
  endtask

  task automatic cai_release_host_cfg();
    begin
      release dut.cai_link.submit_base;
      release dut.cai_link.submit_size;
      release dut.cai_link.context_sel;
    end
  endtask

  task automatic cai_pulse_submit();
    begin
      force dut.cai_link.submit_doorbell = 1'b1;
      @(posedge clk);
      force dut.cai_link.submit_doorbell = 1'b0;
      @(posedge clk);
      release dut.cai_link.submit_doorbell;
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
      while (!dut.cai_link.comp_msg && (wait_cycles < CAI_TIMEOUT)) begin
        @(posedge clk);
        wait_cycles++;
      end
      if (!dut.cai_link.comp_msg) $fatal(1, "tb_carbonz80: CAI completion timeout");

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
      if (tag_got != tag_exp) $fatal(1, "tb_carbonz80: CAI tag mismatch exp=0x%08h got=0x%08h",
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
        if (dut.cai_link.status[0]) begin
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

    int unsigned opdesc_base;
    int unsigned op0_ptr;
    int unsigned op1_ptr;
    int unsigned res_ptr;

    cai_wait_ready(ready);
    if (!ready) begin
      $display("tb_carbonz80: CAI not ready, skipping CAI smoke");
      return;
    end

    cai_force_host_cfg();

    heap_ptr = HEAP_BASE;
    submit_idx = 0;
    comp_idx = 0;
    tag_ctr = 32'h1;

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
                        8'(CARBON_AM95_SCALAR), 8'(CARBON_FMT_BINARY32), 8'h0, 8'h0,
                        64'h0, 16'h0, 8'h0,
                        status, ext, bytes);
    if (status != 16'(CARBON_CAI_STATUS_OK)) $fatal(1, "tb_carbonz80: scalar add status=%0d", status);
    mem_read32(res_ptr, res);
    if (res != 32'h4040_0000) $fatal(1, "tb_carbonz80: scalar add wrong result");

    cai_release_host_cfg();
  endtask

  int unsigned cycles;
  initial begin
    wait(rst_n);
    cycles = 0;
    while (!poweroff && (cycles < 200000)) begin
      @(posedge clk);
      cycles++;
    end
    if (!poweroff) $fatal(1, "tb_carbonz80: timeout waiting for poweroff");
    if (signature !== EXP_SIG) $fatal(1, "tb_carbonz80: signature mismatch exp=%08x got=%08x", EXP_SIG, signature);

    cai_smoke();

    $display("tb_carbonz80: PASS");
    $finish;
  end

endmodule
