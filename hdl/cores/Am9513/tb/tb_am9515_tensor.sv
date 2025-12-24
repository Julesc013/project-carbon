`timescale 1ns/1ps

module tb_am9515_tensor;
  import carbon_arch_pkg::*;
  import am9513_pkg::*;
  import cai_bfm_pkg::*;

  localparam int unsigned MEM_BYTES = 32768;

  localparam int unsigned SUBMIT_ENTRIES = 16;
  localparam int unsigned SUBMIT_MASK    = SUBMIT_ENTRIES - 1;
  localparam int unsigned COMP_ENTRIES   = 16;
  localparam int unsigned COMP_MASK      = COMP_ENTRIES - 1;

  localparam logic [63:0] SUBMIT_BASE = 64'h0000_0000_0000_0100;
  localparam logic [63:0] COMP_BASE   = 64'h0000_0000_0000_0600;
  localparam int unsigned HEAP_BASE   = 32'h0000_1000;

  logic clk;
  logic rst_n;

  initial clk = 1'b0;
  always #5 clk = ~clk;

  initial begin
    rst_n = 1'b0;
    repeat (5) @(posedge clk);
    rst_n = 1'b1;
  end

  csr_if   csr   (.clk(clk), .rst_n(rst_n));
  fabric_if mem_if(.clk(clk), .rst_n(rst_n));
  cai_if   cai   (.clk(clk), .rst_n(rst_n));

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

  am9513_accel #(
      .NUM_CONTEXTS(64),
      .LEGACY_STACK_DEPTH(16)
  ) dut (
      .clk(clk),
      .rst_n(rst_n),
      .csr(csr),
      .mem_if(mem_if),
      .cai(cai)
  );

  // --------------------------------------------------------------------------
  // Memory helpers
  // --------------------------------------------------------------------------
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

  // --------------------------------------------------------------------------
  // Simple bump allocator
  // --------------------------------------------------------------------------
  int unsigned heap_ptr;
  task automatic heap_alloc(
      input int unsigned bytes,
      input int unsigned align,
      output int unsigned addr
  );
    int unsigned a;
    begin
      a = (heap_ptr + align - 1) & ~(align - 1);
      if ((a + bytes) > MEM_BYTES) $fatal(1, "heap overflow (need %0d)", bytes);
      addr = a;
      heap_ptr = a + bytes;
    end
  endtask

  // --------------------------------------------------------------------------
  // CAI helpers
  // --------------------------------------------------------------------------
  int unsigned submit_idx;
  int unsigned comp_idx;
  logic [31:0] tag_ctr;

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
    begin
      while (1) begin
        @(posedge clk);
        if (cai.comp_msg) break;
      end

      addr = int'(COMP_BASE) + ((comp_idx & COMP_MASK) * CARBON_CAI_COMP_REC_V1_SIZE_BYTES);
      rec = '0;
      for (i = 0; i < CARBON_CAI_COMP_REC_V1_SIZE_BYTES; i++) begin
        rec[(i*8) +: 8] = u_mem.mem[addr + i];
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
                           opcode_group, format_primary, 8'h0, 8'h0,
                           tensor_desc_ptr, tensor_desc_len, tensor_rank, 8'h0);
      cai_write_submit_desc(submit_idx, desc);

      cai.submit_doorbell <= 1'b1;
      @(posedge clk);
      cai.submit_doorbell <= 1'b0;

      cai_wait_completion(tag_got, status, ext_status, bytes_written);
      if (tag_got != tag_exp) $fatal(1, "CAI tag mismatch exp=0x%08h got=0x%08h", tag_exp, tag_got);
      submit_idx++;
    end
  endtask

  // --------------------------------------------------------------------------
  // Test sequence
  // --------------------------------------------------------------------------
  initial begin
    int unsigned i;
    logic fault;
    logic [15:0] status;
    logic [15:0] ext;
    logic [31:0] bytes;

    int unsigned tensor_desc_ptr;
    int unsigned opdesc_base;
    int unsigned op0_ptr, op1_ptr, op2_ptr;
    int unsigned res_ptr;

    logic [TENSOR_BITS-1:0] tdesc;

    wait (rst_n);

    cai.submit_base = SUBMIT_BASE;
    cai.submit_size = 32'(SUBMIT_ENTRIES);
    cai.submit_doorbell = 1'b0;
    cai.context_sel = 16'h0;

    for (i = 0; i < MEM_BYTES; i++) begin
      u_mem.mem[i] = 8'h00;
    end

    bfm.csr_write(CARBON_CSR_AM9513_CAI_COMP_BASE_LO, COMP_BASE[31:0], 4'hF, 2'b01, fault);
    if (fault) $fatal(1, "comp_base_lo fault");
    bfm.csr_write(CARBON_CSR_AM9513_CAI_COMP_BASE_HI, COMP_BASE[63:32], 4'hF, 2'b01, fault);
    if (fault) $fatal(1, "comp_base_hi fault");
    bfm.csr_write(CARBON_CSR_AM9513_CAI_COMP_RING_MASK, 32'(COMP_MASK), 4'hF, 2'b01, fault);
    if (fault) $fatal(1, "comp_mask fault");
    bfm.csr_write(CARBON_CSR_AM9513_CAI_IRQ_ENABLE, 32'h0, 4'hF, 2'b01, fault);
    if (fault) $fatal(1, "irq_en fault");
    bfm.csr_write(CARBON_CSR_AM9513_MODE, {24'h0, AM9513_P4_AM9515}, 4'hF, 2'b01, fault);
    if (fault) $fatal(1, "mode fault");
    bfm.csr_write(CARBON_CSR_AM9513_CTRL, 32'h1, 4'hF, 2'b01, fault);
    if (fault) $fatal(1, "ctrl fault");

    heap_ptr  = HEAP_BASE;
    submit_idx = 0;
    comp_idx   = 0;
    tag_ctr    = 32'h1;

    // ----------------------------------------------------------------------
    // GEMM: 2x2 * 2x2 + C
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

    // A = [1 2; 3 4]
    mem_write32(op0_ptr + 0, 32'h3F80_0000);
    mem_write32(op0_ptr + 4, 32'h4000_0000);
    mem_write32(op0_ptr + 8, 32'h4040_0000);
    mem_write32(op0_ptr + 12, 32'h4080_0000);

    // B = [5 6; 7 8]
    mem_write32(op1_ptr + 0, 32'h40A0_0000);
    mem_write32(op1_ptr + 4, 32'h40C0_0000);
    mem_write32(op1_ptr + 8, 32'h40E0_0000);
    mem_write32(op1_ptr + 12, 32'h4100_0000);

    // C = [1 1; 1 1]
    for (i = 0; i < 4; i++) begin
      mem_write32(op2_ptr + (i*4), 32'h3F80_0000);
    end

    cai_write_operand_desc(opdesc_base, 0, 64'(op0_ptr), 32'd16, 32'd0, 32'h0);
    cai_write_operand_desc(opdesc_base, 1, 64'(op1_ptr), 32'd16, 32'd0, 32'h0);
    cai_write_operand_desc(opdesc_base, 2, 64'(op2_ptr), 32'd16, 32'd0, 32'h0);

    cai_submit_and_wait(am9515_opcode(AM9515_TENSOR_GEMM), 32'h0,
                        16'h0000, 16'd3, 64'(opdesc_base),
                        64'(res_ptr), 32'd16, 32'h0,
                        8'(CARBON_AM95_TENSOR), 8'(CARBON_FMT_BINARY32),
                        64'(tensor_desc_ptr), 16'(CARBON_CAI_TENSOR_DESC_V1_SIZE_BYTES), 8'd3,
                        status, ext, bytes);
    if (status != 16'(CARBON_CAI_STATUS_OK)) $fatal(1, "gemm status=%0d", status);
    if (mem_read32(res_ptr + 0) != 32'h41A0_0000) $fatal(1, "gemm c00 wrong");
    if (mem_read32(res_ptr + 4) != 32'h41B8_0000) $fatal(1, "gemm c01 wrong");
    if (mem_read32(res_ptr + 8) != 32'h4230_0000) $fatal(1, "gemm c10 wrong");
    if (mem_read32(res_ptr + 12) != 32'h424C_0000) $fatal(1, "gemm c11 wrong");

    // Determinism: rerun GEMM, result should match.
    for (i = 0; i < 4; i++) begin
      mem_write32(res_ptr + (i*4), 32'h0000_0000);
    end
    cai_submit_and_wait(am9515_opcode(AM9515_TENSOR_GEMM), 32'h0,
                        16'h0000, 16'd3, 64'(opdesc_base),
                        64'(res_ptr), 32'd16, 32'h0,
                        8'(CARBON_AM95_TENSOR), 8'(CARBON_FMT_BINARY32),
                        64'(tensor_desc_ptr), 16'(CARBON_CAI_TENSOR_DESC_V1_SIZE_BYTES), 8'd3,
                        status, ext, bytes);
    if (mem_read32(res_ptr + 0) != 32'h41A0_0000) $fatal(1, "gemm repeat c00 wrong");

    // ----------------------------------------------------------------------
    // DOT: length 4
    // ----------------------------------------------------------------------
    heap_alloc(CARBON_CAI_TENSOR_DESC_V1_SIZE_BYTES, 8, tensor_desc_ptr);
    build_tensor_desc_v1(tdesc, 8'd1, 8'(CARBON_FMT_BINARY32),
                         32'd4, 32'd0, 32'd0, 32'd0,
                         32'd1, 32'd1, 32'd0, 32'd0);
    cai_write_tensor_desc(tensor_desc_ptr, tdesc);

    heap_alloc(CARBON_CAI_OPERAND_DESC_V1_SIZE_BYTES * 2, 8, opdesc_base);
    heap_alloc(16, 4, op0_ptr);
    heap_alloc(16, 4, op1_ptr);
    heap_alloc(4, 4, res_ptr);

    mem_write32(op0_ptr + 0, 32'h3F80_0000);
    mem_write32(op0_ptr + 4, 32'h4000_0000);
    mem_write32(op0_ptr + 8, 32'h4040_0000);
    mem_write32(op0_ptr + 12, 32'h4080_0000);

    mem_write32(op1_ptr + 0, 32'h40A0_0000);
    mem_write32(op1_ptr + 4, 32'h40C0_0000);
    mem_write32(op1_ptr + 8, 32'h40E0_0000);
    mem_write32(op1_ptr + 12, 32'h4100_0000);

    cai_write_operand_desc(opdesc_base, 0, 64'(op0_ptr), 32'd16, 32'd0, 32'h0);
    cai_write_operand_desc(opdesc_base, 1, 64'(op1_ptr), 32'd16, 32'd0, 32'h0);

    cai_submit_and_wait(am9515_opcode(AM9515_TENSOR_DOT), 32'h0,
                        16'h0000, 16'd2, 64'(opdesc_base),
                        64'(res_ptr), 32'd4, 32'h0,
                        8'(CARBON_AM95_TENSOR), 8'(CARBON_FMT_BINARY32),
                        64'(tensor_desc_ptr), 16'(CARBON_CAI_TENSOR_DESC_V1_SIZE_BYTES), 8'd1,
                        status, ext, bytes);
    if (status != 16'(CARBON_CAI_STATUS_OK)) $fatal(1, "dot status=%0d", status);
    if (mem_read32(res_ptr + 0) != 32'h428C_0000) $fatal(1, "dot wrong");

    // ----------------------------------------------------------------------
    // SUM with stride
    // ----------------------------------------------------------------------
    heap_alloc(CARBON_CAI_TENSOR_DESC_V1_SIZE_BYTES, 8, tensor_desc_ptr);
    build_tensor_desc_v1(tdesc, 8'd1, 8'(CARBON_FMT_BINARY32),
                         32'd3, 32'd0, 32'd0, 32'd0,
                         32'd2, 32'd0, 32'd0, 32'd0);
    cai_write_tensor_desc(tensor_desc_ptr, tdesc);

    heap_alloc(CARBON_CAI_OPERAND_DESC_V1_SIZE_BYTES, 8, opdesc_base);
    heap_alloc(32, 4, op0_ptr);
    heap_alloc(4, 4, res_ptr);

    mem_write32(op0_ptr + 0, 32'h3F80_0000);  // 1
    mem_write32(op0_ptr + 8, 32'h4000_0000);  // 2
    mem_write32(op0_ptr + 16, 32'h4040_0000); // 3

    cai_write_operand_desc(opdesc_base, 0, 64'(op0_ptr), 32'd12, 32'd0, 32'h0);

    cai_submit_and_wait(am9515_opcode(AM9515_TENSOR_SUM), 32'h0,
                        16'h0000, 16'd1, 64'(opdesc_base),
                        64'(res_ptr), 32'd4, 32'h0,
                        8'(CARBON_AM95_TENSOR), 8'(CARBON_FMT_BINARY32),
                        64'(tensor_desc_ptr), 16'(CARBON_CAI_TENSOR_DESC_V1_SIZE_BYTES), 8'd1,
                        status, ext, bytes);
    if (status != 16'(CARBON_CAI_STATUS_OK)) $fatal(1, "sum status=%0d", status);
    if (mem_read32(res_ptr + 0) != 32'h40C0_0000) $fatal(1, "sum wrong");

    $display("tb_am9515_tensor: PASS");
    $finish;
  end

endmodule
