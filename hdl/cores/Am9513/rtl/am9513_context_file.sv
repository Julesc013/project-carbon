// Project Carbon - Am9513 accelerator (v1.0)
// am9513_context_file: Per-context state (IEEE env + regfile + legacy stack).

module am9513_context_file #(
    parameter int unsigned NUM_CONTEXTS = 64,
    parameter int unsigned LEGACY_STACK_DEPTH = 16
) (
    input logic clk,
    input logic rst_n,

    input logic [15:0] ctx_sel,
    input logic [3:0]  rf_index,

    output logic [1:0]  rm_rdata,
    output logic [4:0]  flags_rdata,
    output logic [63:0] rf_rdata,
    output logic [127:0] vec_rdata,

    output logic [63:0] stack_top_rdata,
    output logic        stack_empty,
    output logic        stack_full,
    output logic [$clog2(LEGACY_STACK_DEPTH+1)-1:0] stack_depth,

    input logic        rm_we,
    input logic [1:0]  rm_wdata,

    input logic        flags_or_we,
    input logic [4:0]  flags_or_mask,
    input logic        flags_clr_we,
    input logic [4:0]  flags_clr_mask,

    input logic        rf_we,
    input logic [63:0] rf_wdata,

    input logic        vec_we,
    input logic [127:0] vec_wdata,

    input logic        stack_push_we,
    input logic [63:0] stack_push_data,
    input logic        stack_pop_we,

    output logic [63:0] stack_pop_data,
    output logic        stack_overflow_pulse,
    output logic        stack_underflow_pulse
);
  import carbon_arch_pkg::*;

  localparam int unsigned SP_W =
      (LEGACY_STACK_DEPTH < 2) ? 1 : $clog2(LEGACY_STACK_DEPTH + 1);

  logic [1:0] rm_q    [NUM_CONTEXTS];
  logic [4:0] flags_q [NUM_CONTEXTS];
  logic [63:0] rf_q   [NUM_CONTEXTS][16];
  logic [127:0] vec_q [NUM_CONTEXTS][16];

  logic [SP_W-1:0] sp_q [NUM_CONTEXTS];
  logic [63:0] stack_q [NUM_CONTEXTS][LEGACY_STACK_DEPTH];

  logic ctx_valid;
  logic [$clog2(NUM_CONTEXTS)-1:0] ctx_idx;

  always_comb begin
    ctx_valid = (int'(ctx_sel) < int'(NUM_CONTEXTS));
    ctx_idx = '0;
    if (ctx_valid) ctx_idx = ctx_sel[$clog2(NUM_CONTEXTS)-1:0];
  end

  // Combinational reads.
  always_comb begin
    rm_rdata    = 2'(CARBON_RND_RN);
    flags_rdata = '0;
    rf_rdata    = '0;
    vec_rdata   = '0;
    stack_top_rdata = '0;
    stack_empty = 1'b1;
    stack_full  = 1'b0;
    stack_depth = '0;

    if (ctx_valid) begin
      rm_rdata    = rm_q[ctx_idx];
      flags_rdata = flags_q[ctx_idx];
      rf_rdata    = rf_q[ctx_idx][rf_index];
      vec_rdata   = vec_q[ctx_idx][rf_index];
      stack_depth = sp_q[ctx_idx];
      stack_empty = (sp_q[ctx_idx] == '0);
      stack_full  = (sp_q[ctx_idx] == SP_W'(LEGACY_STACK_DEPTH));
      if (sp_q[ctx_idx] != '0) begin
        stack_top_rdata = stack_q[ctx_idx][int'(sp_q[ctx_idx]) - 1];
      end
    end
  end

  assign stack_pop_data = stack_top_rdata;

  // Write/update path.
  always_ff @(posedge clk or negedge rst_n) begin
    int unsigned c;
    int unsigned i;
    if (!rst_n) begin
      stack_overflow_pulse  <= 1'b0;
      stack_underflow_pulse <= 1'b0;
      for (c = 0; c < NUM_CONTEXTS; c++) begin
        rm_q[c] <= 2'(CARBON_RND_RN);
        flags_q[c] <= '0;
        sp_q[c] <= '0;
        for (i = 0; i < 16; i++) begin
          rf_q[c][i] <= '0;
          vec_q[c][i] <= '0;
        end
        for (i = 0; i < LEGACY_STACK_DEPTH; i++) begin
          stack_q[c][i] <= '0;
        end
      end
    end else begin
      stack_overflow_pulse  <= 1'b0;
      stack_underflow_pulse <= 1'b0;

      if (ctx_valid) begin
        if (rm_we) rm_q[ctx_idx] <= rm_wdata;

        if (flags_or_we) flags_q[ctx_idx] <= flags_q[ctx_idx] | flags_or_mask;
        if (flags_clr_we) flags_q[ctx_idx] <= flags_q[ctx_idx] & ~flags_clr_mask;

        if (rf_we) rf_q[ctx_idx][rf_index] <= rf_wdata;
        if (vec_we) vec_q[ctx_idx][rf_index] <= vec_wdata;

        unique case ({stack_push_we, stack_pop_we})
          2'b01: begin
            if (sp_q[ctx_idx] == '0) begin
              stack_underflow_pulse <= 1'b1;
            end else begin
              sp_q[ctx_idx] <= sp_q[ctx_idx] - 1'b1;
            end
          end

          2'b10: begin
            if (sp_q[ctx_idx] == SP_W'(LEGACY_STACK_DEPTH)) begin
              stack_overflow_pulse <= 1'b1;
            end else begin
              stack_q[ctx_idx][int'(sp_q[ctx_idx])] <= stack_push_data;
              sp_q[ctx_idx] <= sp_q[ctx_idx] + 1'b1;
            end
          end

          2'b11: begin
            if (sp_q[ctx_idx] == '0) begin
              stack_underflow_pulse <= 1'b1;
              if (sp_q[ctx_idx] != SP_W'(LEGACY_STACK_DEPTH)) begin
                stack_q[ctx_idx][int'(sp_q[ctx_idx])] <= stack_push_data;
                sp_q[ctx_idx] <= sp_q[ctx_idx] + 1'b1;
              end else begin
                stack_overflow_pulse <= 1'b1;
              end
            end else begin
              // Replace-top: pop then push in one cycle.
              stack_q[ctx_idx][int'(sp_q[ctx_idx]) - 1] <= stack_push_data;
            end
          end

          default: begin
          end
        endcase
      end
    end
  end

endmodule : am9513_context_file
