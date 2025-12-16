`timescale 1ns/1ps

module tb_am9513;
  import carbon_arch_pkg::*;
  import am9513_pkg::*;
  import cai_bfm_pkg::*;

  localparam int unsigned MEM_BYTES = 16384;

  localparam int unsigned SUBMIT_ENTRIES = 16;
  localparam int unsigned SUBMIT_MASK    = SUBMIT_ENTRIES - 1;
  localparam int unsigned COMP_ENTRIES   = 16;
  localparam int unsigned COMP_MASK      = COMP_ENTRIES - 1;

  localparam logic [63:0] SUBMIT_BASE = 64'h0000_0000_0000_0100;
  localparam logic [63:0] COMP_BASE   = 64'h0000_0000_0000_0500;
  localparam int unsigned HEAP_BASE   = 32'h0000_0800;

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
  // Memory helpers (backing store is fabric_mem_bfm internal array)
  // --------------------------------------------------------------------------
  task automatic mem_write8(input int unsigned addr, input logic [7:0] data);
    if (addr >= MEM_BYTES) $fatal(1, "mem_write8 OOB addr=0x%0h", addr);
    u_mem.mem[addr] = data;
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

  task automatic mem_write64(input int unsigned addr, input logic [63:0] data);
    mem_write32(addr + 0, data[31:0]);
    mem_write32(addr + 4, data[63:32]);
  endtask

  function automatic logic [15:0] mem_read16(input int unsigned addr);
    logic [15:0] v;
    begin
      v[7:0]  = u_mem.mem[addr + 0];
      v[15:8] = u_mem.mem[addr + 1];
      mem_read16 = v;
    end
  endfunction

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

  function automatic logic [63:0] mem_read64(input int unsigned addr);
    logic [63:0] v;
    begin
      v[31:0]  = mem_read32(addr + 0);
      v[63:32] = mem_read32(addr + 4);
      mem_read64 = v;
    end
  endfunction

  // --------------------------------------------------------------------------
  // Simple bump allocator for operand/result buffers
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
      input logic [31:0] flags
  );
    int unsigned a;
    begin
      a = base + op_index * CARBON_CAI_OPERAND_DESC_V1_SIZE_BYTES;
      mem_write64(a + CARBON_CAI_OPERAND_DESC_V1_OFF_PTR, ptr);
      mem_write32(a + CARBON_CAI_OPERAND_DESC_V1_OFF_LEN, len);
      mem_write32(a + CARBON_CAI_OPERAND_DESC_V1_OFF_STRIDE, 32'h0);
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
    begin
      while (1) begin
        @(posedge clk);
        if (cai.comp_doorbell) break;
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
                           operands_ptr, result_ptr, result_len, result_stride);
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
  // CSR helpers
  // --------------------------------------------------------------------------
  task automatic csr_set_ctx(input logic [15:0] ctx);
    logic fault;
    begin
      bfm.csr_write(CARBON_CSR_AM9513_CTX_SEL, {16'h0, ctx}, 4'hF, 2'b00, fault);
      if (fault) $fatal(1, "ctx_sel write fault");
    end
  endtask

  task automatic csr_clear_flags(input logic [15:0] ctx);
    logic fault;
    begin
      csr_set_ctx(ctx);
      bfm.csr_write(CARBON_CSR_AM9513_CTX_FLAGS_CLR, 32'h0000_001F, 4'hF, 2'b00, fault);
      if (fault) $fatal(1, "flags_clr write fault");
    end
  endtask

  task automatic csr_set_rm(input logic [15:0] ctx, input logic [1:0] rm);
    logic fault;
    begin
      csr_set_ctx(ctx);
      bfm.csr_write(CARBON_CSR_AM9513_CTX_RM, {30'h0, rm}, 4'hF, 2'b00, fault);
      if (fault) $fatal(1, "rm write fault");
    end
  endtask

  function automatic logic [4:0] csr_read_flags(input logic [15:0] ctx);
    logic fault;
    logic [31:0] rdata;
    begin
      csr_set_ctx(ctx);
      bfm.csr_read(CARBON_CSR_AM9513_CTX_FLAGS, 2'b00, rdata, fault);
      if (fault) $fatal(1, "flags read fault");
      csr_read_flags = rdata[4:0];
    end
  endfunction

  task automatic csr_rf_write64(input logic [15:0] ctx, input logic [3:0] rf, input logic [63:0] data);
    logic fault;
    begin
      csr_set_ctx(ctx);
      bfm.csr_write(CARBON_CSR_AM9513_RF_INDEX, {28'h0, rf}, 4'hF, 2'b00, fault);
      if (fault) $fatal(1, "rf_index write fault");
      bfm.csr_write(CARBON_CSR_AM9513_RF_DATA_LO, data[31:0], 4'hF, 2'b00, fault);
      if (fault) $fatal(1, "rf_lo write fault");
      bfm.csr_write(CARBON_CSR_AM9513_RF_DATA_HI, data[63:32], 4'hF, 2'b00, fault);
      if (fault) $fatal(1, "rf_hi write fault");
    end
  endtask

  function automatic logic [63:0] csr_rf_read64(input logic [15:0] ctx, input logic [3:0] rf);
    logic fault;
    logic [31:0] lo;
    logic [31:0] hi;
    begin
      csr_set_ctx(ctx);
      bfm.csr_write(CARBON_CSR_AM9513_RF_INDEX, {28'h0, rf}, 4'hF, 2'b00, fault);
      if (fault) $fatal(1, "rf_index write fault");
      bfm.csr_read(CARBON_CSR_AM9513_RF_DATA_LO, 2'b00, lo, fault);
      if (fault) $fatal(1, "rf_lo read fault");
      bfm.csr_read(CARBON_CSR_AM9513_RF_DATA_HI, 2'b00, hi, fault);
      if (fault) $fatal(1, "rf_hi read fault");
      csr_rf_read64 = {hi, lo};
    end
  endfunction

  // --------------------------------------------------------------------------
  // Legacy helpers
  // --------------------------------------------------------------------------
  task automatic legacy_push64(input logic [63:0] v);
    logic fault;
    begin
      bfm.csr_write(CARBON_CSR_AM9513_LEGACY_PUSH_LO, v[31:0], 4'hF, 2'b00, fault);
      if (fault) $fatal(1, "legacy push lo fault");
      bfm.csr_write(CARBON_CSR_AM9513_LEGACY_PUSH_HI, v[63:32], 4'hF, 2'b00, fault);
      if (fault) $fatal(1, "legacy push hi fault");
    end
  endtask

  function automatic logic [63:0] legacy_pop64();
    logic fault;
    logic [31:0] lo;
    logic [31:0] hi;
    begin
      bfm.csr_read(CARBON_CSR_AM9513_LEGACY_POP_LO, 2'b00, lo, fault);
      if (fault) $fatal(1, "legacy pop lo fault");
      bfm.csr_read(CARBON_CSR_AM9513_LEGACY_POP_HI, 2'b00, hi, fault);
      if (fault) $fatal(1, "legacy pop hi fault");
      legacy_pop64 = {hi, lo};
    end
  endfunction

  task automatic legacy_issue(input logic [7:0] op);
    logic fault;
    begin
      bfm.csr_write(CARBON_CSR_AM9513_LEGACY_OP, {24'h0, op}, 4'hF, 2'b00, fault);
      if (fault) $fatal(1, "legacy op fault");
      repeat (5) @(posedge clk);
      while (1) begin
        logic [31:0] s;
        bfm.csr_read(CARBON_CSR_AM9513_LEGACY_STATUS, 2'b00, s, fault);
        if (fault) $fatal(1, "legacy status fault");
        if (!s[0]) break;
        @(posedge clk);
      end
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

    int unsigned opdesc_base;
    int unsigned op0_ptr, op1_ptr, op2_ptr;
    int unsigned res_ptr;

    wait (rst_n);

    // Host-side init for CAI link.
    cai.submit_desc_base = SUBMIT_BASE;
    cai.submit_ring_mask = 32'(SUBMIT_MASK);
    cai.submit_doorbell  = 1'b0;
    cai.context_sel      = 16'h0;

    // Clear backing memory.
    for (i = 0; i < MEM_BYTES; i++) begin
      u_mem.mem[i] = 8'h00;
    end

    // Configure device CSRs (privileged where applicable).
    bfm.csr_write(CARBON_CSR_AM9513_CAI_COMP_BASE_LO, COMP_BASE[31:0], 4'hF, 2'b01, fault);
    if (fault) $fatal(1, "comp_base_lo fault");
    bfm.csr_write(CARBON_CSR_AM9513_CAI_COMP_BASE_HI, COMP_BASE[63:32], 4'hF, 2'b01, fault);
    if (fault) $fatal(1, "comp_base_hi fault");
    bfm.csr_write(CARBON_CSR_AM9513_CAI_COMP_RING_MASK, 32'(COMP_MASK), 4'hF, 2'b01, fault);
    if (fault) $fatal(1, "comp_mask fault");
    bfm.csr_write(CARBON_CSR_AM9513_CAI_IRQ_ENABLE, 32'h0, 4'hF, 2'b01, fault);
    if (fault) $fatal(1, "irq_en fault");
    bfm.csr_write(CARBON_CSR_AM9513_MODE, {24'h0, AM9513_P7_TURBO}, 4'hF, 2'b01, fault);
    if (fault) $fatal(1, "mode fault");
    bfm.csr_write(CARBON_CSR_AM9513_CTRL, 32'h1, 4'hF, 2'b01, fault);
    if (fault) $fatal(1, "ctrl fault");

    heap_ptr  = HEAP_BASE;
    submit_idx = 0;
    comp_idx   = 0;
    tag_ctr    = 32'h1;

    csr_clear_flags(16'h0000);
    csr_clear_flags(16'h0001);

    // ----------------------------------------------------------------------
    // CAI: FP32 add/mul/fma
    // ----------------------------------------------------------------------
    heap_alloc(CARBON_CAI_OPERAND_DESC_V1_SIZE_BYTES * 2, 8, opdesc_base);
    heap_alloc(4, 4, op0_ptr);
    heap_alloc(4, 4, op1_ptr);
    heap_alloc(4, 4, res_ptr);
    mem_write32(op0_ptr, 32'h3F80_0000); // 1.0
    mem_write32(op1_ptr, 32'h4000_0000); // 2.0
    cai_write_operand_desc(opdesc_base, 0, 64'(op0_ptr), 32'd4, 32'h0);
    cai_write_operand_desc(opdesc_base, 1, 64'(op1_ptr), 32'd4, 32'h0);
    cai_submit_and_wait(am9513_opcode(AM9513_FUNC_ADD, 8'(CARBON_FMT_BINARY32)), 32'h0,
                        16'h0000, 16'd2, 64'(opdesc_base), 64'(res_ptr), 32'd4, 32'h0,
                        status, ext, bytes);
    if (status != 16'(CARBON_CAI_STATUS_OK)) $fatal(1, "fp32 add status=%0d", status);
    if (mem_read32(res_ptr) != 32'h4040_0000) $fatal(1, "fp32 add wrong result");

    heap_alloc(CARBON_CAI_OPERAND_DESC_V1_SIZE_BYTES * 2, 8, opdesc_base);
    heap_alloc(4, 4, op0_ptr);
    heap_alloc(4, 4, op1_ptr);
    heap_alloc(4, 4, res_ptr);
    mem_write32(op0_ptr, 32'h3FC0_0000); // 1.5
    mem_write32(op1_ptr, 32'h4000_0000); // 2.0
    cai_write_operand_desc(opdesc_base, 0, 64'(op0_ptr), 32'd4, 32'h0);
    cai_write_operand_desc(opdesc_base, 1, 64'(op1_ptr), 32'd4, 32'h0);
    cai_submit_and_wait(am9513_opcode(AM9513_FUNC_MUL, 8'(CARBON_FMT_BINARY32)), 32'h0,
                        16'h0000, 16'd2, 64'(opdesc_base), 64'(res_ptr), 32'd4, 32'h0,
                        status, ext, bytes);
    if (status != 16'(CARBON_CAI_STATUS_OK)) $fatal(1, "fp32 mul status=%0d", status);
    if (mem_read32(res_ptr) != 32'h4040_0000) $fatal(1, "fp32 mul wrong result");

    heap_alloc(CARBON_CAI_OPERAND_DESC_V1_SIZE_BYTES * 3, 8, opdesc_base);
    heap_alloc(4, 4, op0_ptr);
    heap_alloc(4, 4, op1_ptr);
    heap_alloc(4, 4, op2_ptr);
    heap_alloc(4, 4, res_ptr);
    mem_write32(op0_ptr, 32'h4000_0000); // 2.0
    mem_write32(op1_ptr, 32'h4040_0000); // 3.0
    mem_write32(op2_ptr, 32'h4080_0000); // 4.0
    cai_write_operand_desc(opdesc_base, 0, 64'(op0_ptr), 32'd4, 32'h0);
    cai_write_operand_desc(opdesc_base, 1, 64'(op1_ptr), 32'd4, 32'h0);
    cai_write_operand_desc(opdesc_base, 2, 64'(op2_ptr), 32'd4, 32'h0);
    cai_submit_and_wait(am9513_opcode(AM9513_FUNC_FMA, 8'(CARBON_FMT_BINARY32)), 32'h0,
                        16'h0000, 16'd3, 64'(opdesc_base), 64'(res_ptr), 32'd4, 32'h0,
                        status, ext, bytes);
    if (status != 16'(CARBON_CAI_STATUS_OK)) $fatal(1, "fp32 fma status=%0d", status);
    if (mem_read32(res_ptr) != 32'h4120_0000) $fatal(1, "fp32 fma wrong result");

    // ----------------------------------------------------------------------
    // CAI: FP64 add/mul/fma
    // ----------------------------------------------------------------------
    heap_alloc(CARBON_CAI_OPERAND_DESC_V1_SIZE_BYTES * 2, 8, opdesc_base);
    heap_alloc(8, 8, op0_ptr);
    heap_alloc(8, 8, op1_ptr);
    heap_alloc(8, 8, res_ptr);
    mem_write64(op0_ptr, 64'h3FF0_0000_0000_0000); // 1.0
    mem_write64(op1_ptr, 64'h4000_0000_0000_0000); // 2.0
    cai_write_operand_desc(opdesc_base, 0, 64'(op0_ptr), 32'd8, 32'h0);
    cai_write_operand_desc(opdesc_base, 1, 64'(op1_ptr), 32'd8, 32'h0);
    cai_submit_and_wait(am9513_opcode(AM9513_FUNC_ADD, 8'(CARBON_FMT_BINARY64)), 32'h0,
                        16'h0000, 16'd2, 64'(opdesc_base), 64'(res_ptr), 32'd8, 32'h0,
                        status, ext, bytes);
    if (status != 16'(CARBON_CAI_STATUS_OK)) $fatal(1, "fp64 add status=%0d", status);
    if (mem_read64(res_ptr) != 64'h4008_0000_0000_0000) $fatal(1, "fp64 add wrong result");

    heap_alloc(CARBON_CAI_OPERAND_DESC_V1_SIZE_BYTES * 2, 8, opdesc_base);
    heap_alloc(8, 8, op0_ptr);
    heap_alloc(8, 8, op1_ptr);
    heap_alloc(8, 8, res_ptr);
    mem_write64(op0_ptr, 64'h3FF8_0000_0000_0000); // 1.5
    mem_write64(op1_ptr, 64'h4000_0000_0000_0000); // 2.0
    cai_write_operand_desc(opdesc_base, 0, 64'(op0_ptr), 32'd8, 32'h0);
    cai_write_operand_desc(opdesc_base, 1, 64'(op1_ptr), 32'd8, 32'h0);
    cai_submit_and_wait(am9513_opcode(AM9513_FUNC_MUL, 8'(CARBON_FMT_BINARY64)), 32'h0,
                        16'h0000, 16'd2, 64'(opdesc_base), 64'(res_ptr), 32'd8, 32'h0,
                        status, ext, bytes);
    if (status != 16'(CARBON_CAI_STATUS_OK)) $fatal(1, "fp64 mul status=%0d", status);
    if (mem_read64(res_ptr) != 64'h4008_0000_0000_0000) $fatal(1, "fp64 mul wrong result");

    heap_alloc(CARBON_CAI_OPERAND_DESC_V1_SIZE_BYTES * 3, 8, opdesc_base);
    heap_alloc(8, 8, op0_ptr);
    heap_alloc(8, 8, op1_ptr);
    heap_alloc(8, 8, op2_ptr);
    heap_alloc(8, 8, res_ptr);
    mem_write64(op0_ptr, 64'h4000_0000_0000_0000); // 2.0
    mem_write64(op1_ptr, 64'h4008_0000_0000_0000); // 3.0
    mem_write64(op2_ptr, 64'h4010_0000_0000_0000); // 4.0
    cai_write_operand_desc(opdesc_base, 0, 64'(op0_ptr), 32'd8, 32'h0);
    cai_write_operand_desc(opdesc_base, 1, 64'(op1_ptr), 32'd8, 32'h0);
    cai_write_operand_desc(opdesc_base, 2, 64'(op2_ptr), 32'd8, 32'h0);
    cai_submit_and_wait(am9513_opcode(AM9513_FUNC_FMA, 8'(CARBON_FMT_BINARY64)), 32'h0,
                        16'h0000, 16'd3, 64'(opdesc_base), 64'(res_ptr), 32'd8, 32'h0,
                        status, ext, bytes);
    if (status != 16'(CARBON_CAI_STATUS_OK)) $fatal(1, "fp64 fma status=%0d", status);
    if (mem_read64(res_ptr) != 64'h4024_0000_0000_0000) $fatal(1, "fp64 fma wrong result");

    // ----------------------------------------------------------------------
    // CAI: conversions (FP16/BF16/FP32)
    // ----------------------------------------------------------------------
    heap_alloc(CARBON_CAI_OPERAND_DESC_V1_SIZE_BYTES, 8, opdesc_base);
    heap_alloc(2, 2, op0_ptr);
    heap_alloc(4, 4, res_ptr);
    mem_write16(op0_ptr, 16'h3E00); // fp16 1.5
    cai_write_operand_desc(opdesc_base, 0, 64'(op0_ptr), 32'd2, 32'h0);
    cai_submit_and_wait(am9513_opcode(AM9513_FUNC_CONV, 8'(CARBON_FMT_BINARY32)), 32'(CARBON_FMT_BINARY16),
                        16'h0000, 16'd1, 64'(opdesc_base), 64'(res_ptr), 32'd4, 32'h0,
                        status, ext, bytes);
    if (status != 16'(CARBON_CAI_STATUS_OK)) $fatal(1, "fp16->fp32 status=%0d", status);
    if (mem_read32(res_ptr) != 32'h3FC0_0000) $fatal(1, "fp16->fp32 wrong result");

    heap_alloc(CARBON_CAI_OPERAND_DESC_V1_SIZE_BYTES, 8, opdesc_base);
    heap_alloc(2, 2, op0_ptr);
    heap_alloc(4, 4, res_ptr);
    mem_write16(op0_ptr, 16'h3F80); // bf16 1.0
    cai_write_operand_desc(opdesc_base, 0, 64'(op0_ptr), 32'd2, 32'h0);
    cai_submit_and_wait(am9513_opcode(AM9513_FUNC_CONV, 8'(CARBON_FMT_BINARY32)), 32'(CARBON_FMT_BFLOAT16),
                        16'h0000, 16'd1, 64'(opdesc_base), 64'(res_ptr), 32'd4, 32'h0,
                        status, ext, bytes);
    if (status != 16'(CARBON_CAI_STATUS_OK)) $fatal(1, "bf16->fp32 status=%0d", status);
    if (mem_read32(res_ptr) != 32'h3F80_0000) $fatal(1, "bf16->fp32 wrong result");

    heap_alloc(CARBON_CAI_OPERAND_DESC_V1_SIZE_BYTES, 8, opdesc_base);
    heap_alloc(4, 4, op0_ptr);
    heap_alloc(2, 2, res_ptr);
    mem_write32(op0_ptr, 32'h3F80_0000); // fp32 1.0
    cai_write_operand_desc(opdesc_base, 0, 64'(op0_ptr), 32'd4, 32'h0);
    cai_submit_and_wait(am9513_opcode(AM9513_FUNC_CONV, 8'(CARBON_FMT_BINARY16)), 32'(CARBON_FMT_BINARY32),
                        16'h0000, 16'd1, 64'(opdesc_base), 64'(res_ptr), 32'd2, 32'h0,
                        status, ext, bytes);
    if (status != 16'(CARBON_CAI_STATUS_OK)) $fatal(1, "fp32->fp16 status=%0d", status);
    if (mem_read16(res_ptr) != 16'h3C00) $fatal(1, "fp32->fp16 wrong result");

    heap_alloc(CARBON_CAI_OPERAND_DESC_V1_SIZE_BYTES, 8, opdesc_base);
    heap_alloc(4, 4, op0_ptr);
    heap_alloc(2, 2, res_ptr);
    mem_write32(op0_ptr, 32'h3F80_0000); // fp32 1.0
    cai_write_operand_desc(opdesc_base, 0, 64'(op0_ptr), 32'd4, 32'h0);
    cai_submit_and_wait(am9513_opcode(AM9513_FUNC_CONV, 8'(CARBON_FMT_BFLOAT16)), 32'(CARBON_FMT_BINARY32),
                        16'h0000, 16'd1, 64'(opdesc_base), 64'(res_ptr), 32'd2, 32'h0,
                        status, ext, bytes);
    if (status != 16'(CARBON_CAI_STATUS_OK)) $fatal(1, "fp32->bf16 status=%0d", status);
    if (mem_read16(res_ptr) != 16'h3F80) $fatal(1, "fp32->bf16 wrong result");

    // ----------------------------------------------------------------------
    // CAI: sqrt + exp/log sanity + sincos multi-result
    // ----------------------------------------------------------------------
    heap_alloc(CARBON_CAI_OPERAND_DESC_V1_SIZE_BYTES, 8, opdesc_base);
    heap_alloc(4, 4, op0_ptr);
    heap_alloc(4, 4, res_ptr);
    mem_write32(op0_ptr, 32'h4080_0000); // 4.0
    cai_write_operand_desc(opdesc_base, 0, 64'(op0_ptr), 32'd4, 32'h0);
    cai_submit_and_wait(am9513_opcode(AM9513_FUNC_SQRT, 8'(CARBON_FMT_BINARY32)), 32'h0,
                        16'h0000, 16'd1, 64'(opdesc_base), 64'(res_ptr), 32'd4, 32'h0,
                        status, ext, bytes);
    if (status != 16'(CARBON_CAI_STATUS_OK)) $fatal(1, "sqrt status=%0d", status);
    if (mem_read32(res_ptr) != 32'h4000_0000) $fatal(1, "sqrt wrong result");

    // exp(0)=1
    heap_alloc(CARBON_CAI_OPERAND_DESC_V1_SIZE_BYTES, 8, opdesc_base);
    heap_alloc(4, 4, op0_ptr);
    heap_alloc(4, 4, res_ptr);
    mem_write32(op0_ptr, 32'h0000_0000);
    cai_write_operand_desc(opdesc_base, 0, 64'(op0_ptr), 32'd4, 32'h0);
    cai_submit_and_wait(am9513_opcode(AM9513_FUNC_EXP, 8'(CARBON_FMT_BINARY32)), 32'h0,
                        16'h0000, 16'd1, 64'(opdesc_base), 64'(res_ptr), 32'd4, 32'h0,
                        status, ext, bytes);
    if (status != 16'(CARBON_CAI_STATUS_OK)) $fatal(1, "exp status=%0d", status);
    if (mem_read32(res_ptr) != 32'h3F80_0000) $fatal(1, "exp(0) wrong");

    // exp(1) sanity: 1 < exp(1) < 4
    heap_alloc(CARBON_CAI_OPERAND_DESC_V1_SIZE_BYTES, 8, opdesc_base);
    heap_alloc(4, 4, op0_ptr);
    heap_alloc(4, 4, res_ptr);
    mem_write32(op0_ptr, 32'h3F80_0000);
    cai_write_operand_desc(opdesc_base, 0, 64'(op0_ptr), 32'd4, 32'h0);
    cai_submit_and_wait(am9513_opcode(AM9513_FUNC_EXP, 8'(CARBON_FMT_BINARY32)), 32'h0,
                        16'h0000, 16'd1, 64'(opdesc_base), 64'(res_ptr), 32'd4, 32'h0,
                        status, ext, bytes);
    if (status != 16'(CARBON_CAI_STATUS_OK)) $fatal(1, "exp(1) status=%0d", status);
    if (!(mem_read32(res_ptr) > 32'h3F80_0000)) $fatal(1, "exp(1) not > 1.0");
    if (!(mem_read32(res_ptr) < 32'h4080_0000)) $fatal(1, "exp(1) not < 4.0");

    // log(1)=0
    heap_alloc(CARBON_CAI_OPERAND_DESC_V1_SIZE_BYTES, 8, opdesc_base);
    heap_alloc(4, 4, op0_ptr);
    heap_alloc(4, 4, res_ptr);
    mem_write32(op0_ptr, 32'h3F80_0000);
    cai_write_operand_desc(opdesc_base, 0, 64'(op0_ptr), 32'd4, 32'h0);
    cai_submit_and_wait(am9513_opcode(AM9513_FUNC_LOG, 8'(CARBON_FMT_BINARY32)), 32'h0,
                        16'h0000, 16'd1, 64'(opdesc_base), 64'(res_ptr), 32'd4, 32'h0,
                        status, ext, bytes);
    if (status != 16'(CARBON_CAI_STATUS_OK)) $fatal(1, "log status=%0d", status);
    if (mem_read32(res_ptr) != 32'h0000_0000) $fatal(1, "log(1) wrong");

    // log(2) sanity: 0 < log(2) < 1
    heap_alloc(CARBON_CAI_OPERAND_DESC_V1_SIZE_BYTES, 8, opdesc_base);
    heap_alloc(4, 4, op0_ptr);
    heap_alloc(4, 4, res_ptr);
    mem_write32(op0_ptr, 32'h4000_0000);
    cai_write_operand_desc(opdesc_base, 0, 64'(op0_ptr), 32'd4, 32'h0);
    cai_submit_and_wait(am9513_opcode(AM9513_FUNC_LOG, 8'(CARBON_FMT_BINARY32)), 32'h0,
                        16'h0000, 16'd1, 64'(opdesc_base), 64'(res_ptr), 32'd4, 32'h0,
                        status, ext, bytes);
    if (status != 16'(CARBON_CAI_STATUS_OK)) $fatal(1, "log(2) status=%0d", status);
    if (!(mem_read32(res_ptr) > 32'h0000_0000)) $fatal(1, "log(2) not > 0");
    if (!(mem_read32(res_ptr) < 32'h3F80_0000)) $fatal(1, "log(2) not < 1.0");

    // sincos(0): sin=0, cos=1 (two results)
    heap_alloc(CARBON_CAI_OPERAND_DESC_V1_SIZE_BYTES, 8, opdesc_base);
    heap_alloc(4, 4, op0_ptr);
    heap_alloc(8, 4, res_ptr);
    mem_write32(op0_ptr, 32'h0000_0000);
    cai_write_operand_desc(opdesc_base, 0, 64'(op0_ptr), 32'd4, 32'h0);
    cai_submit_and_wait(am9513_opcode(AM9513_FUNC_SINCOS, 8'(CARBON_FMT_BINARY32)), 32'h0,
                        16'h0000, 16'd1, 64'(opdesc_base), 64'(res_ptr), 32'd8, 32'h0,
                        status, ext, bytes);
    if (status != 16'(CARBON_CAI_STATUS_OK)) $fatal(1, "sincos status=%0d", status);
    if (mem_read32(res_ptr + 0) != 32'h0000_0000) $fatal(1, "sincos sin wrong");
    if (mem_read32(res_ptr + 4) != 32'h3F80_0000) $fatal(1, "sincos cos wrong");

    // ----------------------------------------------------------------------
    // CAI: exception flags + multi-context isolation
    // ----------------------------------------------------------------------
    csr_clear_flags(16'h0000);
    csr_clear_flags(16'h0001);

    // Context 1: 1.0 / 0.0 should set DZ
    heap_alloc(CARBON_CAI_OPERAND_DESC_V1_SIZE_BYTES * 2, 8, opdesc_base);
    heap_alloc(4, 4, op0_ptr);
    heap_alloc(4, 4, op1_ptr);
    heap_alloc(4, 4, res_ptr);
    mem_write32(op0_ptr, 32'h3F80_0000);
    mem_write32(op1_ptr, 32'h0000_0000);
    cai_write_operand_desc(opdesc_base, 0, 64'(op0_ptr), 32'd4, 32'h0);
    cai_write_operand_desc(opdesc_base, 1, 64'(op1_ptr), 32'd4, 32'h0);
    cai_submit_and_wait(am9513_opcode(AM9513_FUNC_DIV, 8'(CARBON_FMT_BINARY32)), 32'h0,
                        16'h0001, 16'd2, 64'(opdesc_base), 64'(res_ptr), 32'd4, 32'h0,
                        status, ext, bytes);
    if (status != 16'(CARBON_CAI_STATUS_OK)) $fatal(1, "div status=%0d", status);
    if ((ext[4:0] & AM9513_F_DZ) == 0) $fatal(1, "expected DZ in completion ext_status");
    if ((csr_read_flags(16'h0001) & AM9513_F_DZ) == 0) $fatal(1, "expected DZ in ctx1 flags");
    if (csr_read_flags(16'h0000) != 5'h0) $fatal(1, "ctx0 flags should remain clear");

    // Context 0: sqrt(-1) should set NV
    heap_alloc(CARBON_CAI_OPERAND_DESC_V1_SIZE_BYTES, 8, opdesc_base);
    heap_alloc(4, 4, op0_ptr);
    heap_alloc(4, 4, res_ptr);
    mem_write32(op0_ptr, 32'hBF80_0000);
    cai_write_operand_desc(opdesc_base, 0, 64'(op0_ptr), 32'd4, 32'h0);
    cai_submit_and_wait(am9513_opcode(AM9513_FUNC_SQRT, 8'(CARBON_FMT_BINARY32)), 32'h0,
                        16'h0000, 16'd1, 64'(opdesc_base), 64'(res_ptr), 32'd4, 32'h0,
                        status, ext, bytes);
    if (status != 16'(CARBON_CAI_STATUS_OK)) $fatal(1, "sqrt(-1) status=%0d", status);
    if ((ext[4:0] & AM9513_F_NV) == 0) $fatal(1, "expected NV in completion ext_status");
    if ((csr_read_flags(16'h0000) & AM9513_F_NV) == 0) $fatal(1, "expected NV in ctx0 flags");

    // ----------------------------------------------------------------------
    // CAI: register-file fast path + mode override
    // ----------------------------------------------------------------------
    csr_rf_write64(16'h0000, 4'd0, 64'h0000_0000_3F80_0000); // F0 = 1.0f
    csr_rf_write64(16'h0000, 4'd1, 64'h0000_0000_4000_0000); // F1 = 2.0f
    csr_rf_write64(16'h0000, 4'd2, 64'h0);

    heap_alloc(CARBON_CAI_OPERAND_DESC_V1_SIZE_BYTES * 2, 8, opdesc_base);
    cai_write_operand_desc(opdesc_base, 0, 64'h0, 32'h0,
                           (32'(1) << AM9513_OPERAND_FLAG_IS_REG_BIT) |
                           (32'(0) << AM9513_OPERAND_FLAG_REG_LSB));
    cai_write_operand_desc(opdesc_base, 1, 64'h0, 32'h0,
                           (32'(1) << AM9513_OPERAND_FLAG_IS_REG_BIT) |
                           (32'(1) << AM9513_OPERAND_FLAG_REG_LSB));

    // Set default mode to P0 and demonstrate unsupported result-to-reg without override.
    bfm.csr_write(CARBON_CSR_AM9513_MODE, {24'h0, AM9513_P0_AM9511}, 4'hF, 2'b01, fault);
    if (fault) $fatal(1, "mode(P0) fault");

    cai_submit_and_wait(am9513_opcode(AM9513_FUNC_ADD, 8'(CARBON_FMT_BINARY32)),
                        (32'(1) << AM9513_SUBMIT_FLAG_RESULT_REG_BIT) |
                        (32'(2) << AM9513_SUBMIT_FLAG_RESULT_REG_LSB),
                        16'h0000, 16'd2, 64'(opdesc_base), 64'h0, 32'h0, 32'h0,
                        status, ext, bytes);
    if (status != 16'(CARBON_CAI_STATUS_UNSUPPORTED)) $fatal(1, "expected unsupported result-to-reg");

    // Now override to P7 and retry.
    cai_submit_and_wait(am9513_opcode(AM9513_FUNC_ADD, 8'(CARBON_FMT_BINARY32)),
                        (32'(1) << AM9513_SUBMIT_FLAG_MODE_VALID_BIT) |
                        (32'(AM9513_P7_TURBO) << AM9513_SUBMIT_FLAG_MODE_LSB) |
                        (32'(1) << AM9513_SUBMIT_FLAG_RESULT_REG_BIT) |
                        (32'(2) << AM9513_SUBMIT_FLAG_RESULT_REG_LSB),
                        16'h0000, 16'd2, 64'(opdesc_base), 64'h0, 32'h0, 32'h0,
                        status, ext, bytes);
    if (status != 16'(CARBON_CAI_STATUS_OK)) $fatal(1, "result-to-reg status=%0d", status);
    if (csr_rf_read64(16'h0000, 4'd2)[31:0] != 32'h4040_0000) $fatal(1, "rf fastpath wrong");

    // Restore default mode to P7 for remaining tests.
    bfm.csr_write(CARBON_CSR_AM9513_MODE, {24'h0, AM9513_P7_TURBO}, 4'hF, 2'b01, fault);
    if (fault) $fatal(1, "mode(P7) fault");

    // ----------------------------------------------------------------------
    // CAI: float <-> int conversions (minimum coverage)
    // ----------------------------------------------------------------------
    csr_set_rm(16'h0000, 2'(CARBON_RND_RZ));
    heap_alloc(CARBON_CAI_OPERAND_DESC_V1_SIZE_BYTES, 8, opdesc_base);
    heap_alloc(4, 4, op0_ptr);
    heap_alloc(4, 4, res_ptr);
    mem_write32(op0_ptr, 32'h0000_0003); // int32 3
    cai_write_operand_desc(opdesc_base, 0, 64'(op0_ptr), 32'd4, 32'h0);
    cai_submit_and_wait(am9513_opcode(AM9513_FUNC_I32_TO_F32, 8'(CARBON_FMT_BINARY32)), 32'h0,
                        16'h0000, 16'd1, 64'(opdesc_base), 64'(res_ptr), 32'd4, 32'h0,
                        status, ext, bytes);
    if (status != 16'(CARBON_CAI_STATUS_OK)) $fatal(1, "i32->f32 status=%0d", status);
    if (mem_read32(res_ptr) != 32'h4040_0000) $fatal(1, "i32->f32 wrong result");

    heap_alloc(CARBON_CAI_OPERAND_DESC_V1_SIZE_BYTES, 8, opdesc_base);
    heap_alloc(4, 4, op0_ptr);
    heap_alloc(4, 4, res_ptr);
    mem_write32(op0_ptr, 32'h4060_0000); // fp32 3.5
    cai_write_operand_desc(opdesc_base, 0, 64'(op0_ptr), 32'd4, 32'h0);
    cai_submit_and_wait(am9513_opcode(AM9513_FUNC_F32_TO_I32, 8'(CARBON_FMT_BINARY32)), 32'h0,
                        16'h0000, 16'd1, 64'(opdesc_base), 64'(res_ptr), 32'd4, 32'h0,
                        status, ext, bytes);
    if (status != 16'(CARBON_CAI_STATUS_OK)) $fatal(1, "f32->i32 status=%0d", status);
    if (mem_read32(res_ptr) != 32'h0000_0003) $fatal(1, "f32->i32 wrong result");
    if ((ext[4:0] & AM9513_F_NX) == 0) $fatal(1, "expected NX for 3.5->3");

    // ----------------------------------------------------------------------
    // Legacy: 9511 (fp32) push/op/pop
    // ----------------------------------------------------------------------
    csr_set_ctx(16'h0000);
    bfm.csr_write(CARBON_CSR_AM9513_LEGACY_CTRL, 32'h0000_0000, 4'hF, 2'b00, fault);
    if (fault) $fatal(1, "legacy ctrl fault");

    legacy_push64(64'h0000_0000_3F80_0000); // 1.0f
    legacy_push64(64'h0000_0000_4000_0000); // 2.0f
    legacy_issue(AM9513_LEG_OP_ADD);
    if (legacy_pop64()[31:0] != 32'h4040_0000) $fatal(1, "legacy 9511 add wrong");

    legacy_push64(64'h0000_0000_3FC0_0000); // 1.5f
    legacy_push64(64'h0000_0000_4000_0000); // 2.0f
    legacy_issue(AM9513_LEG_OP_MUL);
    if (legacy_pop64()[31:0] != 32'h4040_0000) $fatal(1, "legacy 9511 mul wrong");

    // ----------------------------------------------------------------------
    // Legacy: 9512 (fp32 + fp64) add/mul/div
    // ----------------------------------------------------------------------
    // 9512 fp32 add: 1.5 + 2.25 = 3.75
    bfm.csr_write(CARBON_CSR_AM9513_LEGACY_CTRL,
                  (32'h1 << 0) | (32'(CARBON_FMT_BINARY32) << 4),
                  4'hF, 2'b00, fault);
    if (fault) $fatal(1, "legacy ctrl (p1 fp32) fault");
    legacy_push64(64'h0000_0000_3FC0_0000); // 1.5
    legacy_push64(64'h0000_0000_4010_0000); // 2.25
    legacy_issue(AM9513_LEG_OP_ADD);
    if (legacy_pop64()[31:0] != 32'h4070_0000) $fatal(1, "legacy 9512 fp32 add wrong");

    // 9512 fp32 mul: 1.5 * 2.0 = 3.0
    legacy_push64(64'h0000_0000_3FC0_0000); // 1.5
    legacy_push64(64'h0000_0000_4000_0000); // 2.0
    legacy_issue(AM9513_LEG_OP_MUL);
    if (legacy_pop64()[31:0] != 32'h4040_0000) $fatal(1, "legacy 9512 fp32 mul wrong");

    // 9512 fp32 div: 9.0 / 3.0 = 3.0 (push 9 then 3; DIV computes B/A)
    legacy_push64(64'h0000_0000_4110_0000); // 9.0
    legacy_push64(64'h0000_0000_4040_0000); // 3.0
    legacy_issue(AM9513_LEG_OP_DIV);
    if (legacy_pop64()[31:0] != 32'h4040_0000) $fatal(1, "legacy 9512 fp32 div wrong");

    // 9512 fp64 mul: 2.0 * 3.0 = 6.0
    bfm.csr_write(CARBON_CSR_AM9513_LEGACY_CTRL,
                  (32'h1 << 0) | (32'(CARBON_FMT_BINARY64) << 4),
                  4'hF, 2'b00, fault);
    if (fault) $fatal(1, "legacy ctrl (p1 fp64) fault");

    // 9512 fp64 add: 1.0 + 2.0 = 3.0
    legacy_push64(64'h3FF0_0000_0000_0000); // 1.0
    legacy_push64(64'h4000_0000_0000_0000); // 2.0
    legacy_issue(AM9513_LEG_OP_ADD);
    if (legacy_pop64() != 64'h4008_0000_0000_0000) $fatal(1, "legacy 9512 fp64 add wrong");

    legacy_push64(64'h4000_0000_0000_0000); // 2.0
    legacy_push64(64'h4008_0000_0000_0000); // 3.0
    legacy_issue(AM9513_LEG_OP_MUL);
    if (legacy_pop64() != 64'h4018_0000_0000_0000) $fatal(1, "legacy 9512 fp64 mul wrong");

    // 9512 fp64 div: 8.0 / 2.0 = 4.0 (push 8 then 2; DIV computes B/A)
    legacy_push64(64'h4020_0000_0000_0000); // 8.0
    legacy_push64(64'h4000_0000_0000_0000); // 2.0
    legacy_issue(AM9513_LEG_OP_DIV);
    if (legacy_pop64() != 64'h4010_0000_0000_0000) $fatal(1, "legacy 9512 fp64 div wrong");

    $display("tb_am9513: PASS");
    $finish;
  end

endmodule
