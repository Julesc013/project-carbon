`timescale 1ns/1ps

module tb_cai_contract;
  import carbon_arch_pkg::*;
  import am9513_pkg::*;
  import cai_bfm_pkg::*;

  localparam int unsigned MEM_BYTES = 16384;

  localparam int unsigned SUBMIT_ENTRIES = 8;
  localparam int unsigned SUBMIT_MASK    = SUBMIT_ENTRIES - 1;
  localparam int unsigned COMP_ENTRIES   = 8;
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

  am9513_accel dut (
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
  // CAI descriptor helpers
  // --------------------------------------------------------------------------
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

  function automatic logic [COMP_BITS-1:0] cai_read_comp_rec(input int unsigned idx);
    logic [COMP_BITS-1:0] rec;
    int unsigned base;
    int unsigned i;
    begin
      rec = '0;
      base = int'(COMP_BASE) + ((idx & COMP_MASK) * CARBON_CAI_COMP_REC_V1_SIZE_BYTES);
      for (i = 0; i < CARBON_CAI_COMP_REC_V1_SIZE_BYTES; i++) begin
        rec[(i*8) +: 8] = u_mem.mem[base + i];
      end
      cai_read_comp_rec = rec;
    end
  endfunction

  task automatic wait_comp_doorbell();
    begin
      while (!cai.comp_doorbell) @(posedge clk);
      @(posedge clk);
    end
  endtask

  // --------------------------------------------------------------------------
  // Test sequence
  // --------------------------------------------------------------------------
  initial begin
    logic fault;
    logic [SUBMIT_BITS-1:0] desc;
    logic [31:0] tag;
    logic [15:0] status;
    logic [15:0] ext_status;
    logic [31:0] bytes_written;

    int unsigned opdesc_base;
    int unsigned op0_ptr;
    int unsigned op1_ptr;
    int unsigned res_ptr;

    int unsigned res_ptr_bad;

    wait (rst_n);

    // Host-side CAI wiring (register-level).
    cai.submit_desc_base = SUBMIT_BASE;
    cai.submit_ring_mask = 32'(SUBMIT_MASK);
    cai.submit_doorbell  = 1'b0;
    cai.context_sel      = 16'h0000;

    // Device-side CAI completion config via CSR.
    bfm.csr_write(CARBON_CSR_AM9513_CAI_COMP_BASE_LO, COMP_BASE[31:0], 4'hF, 2'b01, fault);
    if (fault) $fatal(1, "comp_base_lo fault");
    bfm.csr_write(CARBON_CSR_AM9513_CAI_COMP_BASE_HI, COMP_BASE[63:32], 4'hF, 2'b01, fault);
    if (fault) $fatal(1, "comp_base_hi fault");
    bfm.csr_write(CARBON_CSR_AM9513_CAI_COMP_RING_MASK, 32'(COMP_MASK), 4'hF, 2'b01, fault);
    if (fault) $fatal(1, "comp_mask fault");

    // Enable accelerator and default to P7.
    bfm.csr_write(CARBON_CSR_AM9513_MODE, {24'h0, AM9513_P7_TURBO}, 4'hF, 2'b01, fault);
    if (fault) $fatal(1, "mode fault");
    bfm.csr_write(CARBON_CSR_AM9513_ENABLE, 32'h1, 4'hF, 2'b01, fault);
    if (fault) $fatal(1, "enable fault");

    heap_ptr = HEAP_BASE;

    // ----------------------------------------------------------------------
    // Contract: valid descriptor parses + completion implies result visible.
    // ----------------------------------------------------------------------
    heap_alloc(CARBON_CAI_OPERAND_DESC_V1_SIZE_BYTES * 2, 8, opdesc_base);
    heap_alloc(4, 4, op0_ptr);
    heap_alloc(4, 4, op1_ptr);
    heap_alloc(4, 4, res_ptr);

    mem_write32(op0_ptr, 32'h3F80_0000); // 1.0f
    mem_write32(op1_ptr, 32'h4000_0000); // 2.0f
    mem_write32(res_ptr, 32'hDEAD_BEEF);

    cai_write_operand_desc(opdesc_base, 0, 64'(op0_ptr), 32'd4, 32'h0);
    cai_write_operand_desc(opdesc_base, 1, 64'(op1_ptr), 32'd4, 32'h0);

    build_submit_desc_v1(desc,
                         am9513_opcode(AM9513_FUNC_ADD, 8'(CARBON_FMT_BINARY32)),
                         32'h0,
                         16'h0000,
                         16'd2,
                         32'hAABB_CCDD,
                         64'(opdesc_base),
                         64'(res_ptr),
                         32'd4,
                         32'h0);
    cai_write_submit_desc(0, desc);

    cai.submit_doorbell <= 1'b1;
    @(posedge clk);
    cai.submit_doorbell <= 1'b0;

    wait_comp_doorbell();

    decode_comp_rec_v1(cai_read_comp_rec(0), tag, status, ext_status, bytes_written);
    if (tag != 32'hAABB_CCDD) $fatal(1, "comp tag mismatch");
    if (status != 16'(CARBON_CAI_STATUS_OK)) $fatal(1, "comp status=%0d", status);
    if (bytes_written != 32'd4) $fatal(1, "bytes_written=%0d", bytes_written);
    if (ext_status[4:0] != 5'h00) $fatal(1, "unexpected IEEE flags: %0h", ext_status[4:0]);

    if (mem_read32(res_ptr) != 32'h4040_0000) $fatal(1, "result not visible at completion");

    // ----------------------------------------------------------------------
    // Contract: invalid descriptor version returns INVALID_OP.
    // ----------------------------------------------------------------------
    heap_alloc(4, 4, res_ptr_bad);
    mem_write32(res_ptr_bad, 32'h1122_3344);

    build_submit_desc_v1(desc,
                         am9513_opcode(AM9513_FUNC_ADD, 8'(CARBON_FMT_BINARY32)),
                         32'h0,
                         16'h0000,
                         16'd2,
                         32'h1357_9BDF,
                         64'(opdesc_base),
                         64'(res_ptr_bad),
                         32'd4,
                         32'h0);
    desc[(CARBON_CAI_SUBMIT_DESC_V1_OFF_DESC_VERSION*8) +: 16] = 16'(CARBON_CAI_SUBMIT_DESC_V1_VERSION + 1);
    cai_write_submit_desc(1, desc);

    cai.submit_doorbell <= 1'b1;
    @(posedge clk);
    cai.submit_doorbell <= 1'b0;

    wait_comp_doorbell();

    decode_comp_rec_v1(cai_read_comp_rec(1), tag, status, ext_status, bytes_written);
    if (tag != 32'h1357_9BDF) $fatal(1, "comp tag mismatch (bad desc)");
    if (status != 16'(CARBON_CAI_STATUS_INVALID_OP)) $fatal(1, "expected INVALID_OP got=%0d", status);
    if (bytes_written != 32'd0) $fatal(1, "expected bytes_written=0 got=%0d", bytes_written);

    if (mem_read32(res_ptr_bad) != 32'h1122_3344) $fatal(1, "invalid desc should not write result");

    $display("tb_cai_contract: PASS");
    $finish;
  end

endmodule

