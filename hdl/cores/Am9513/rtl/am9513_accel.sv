// Project Carbon - Am9513 accelerator (v1.0)
// am9513_accel: Fabric-attached accelerator with CAI + CSR + legacy shells.

module am9513_accel #(
    parameter int unsigned NUM_CONTEXTS = 64,
    parameter int unsigned LEGACY_STACK_DEPTH = 16
) (
    input logic clk,
    input logic rst_n,

    csr_if.slave csr,
    fabric_if.master mem_if,
    cai_if.dev cai
);
  import carbon_arch_pkg::*;
  import am9513_pkg::*;

  localparam int unsigned CSR_ADDR_W = $bits(csr.req_addr);
  localparam int unsigned CSR_DATA_W = $bits(csr.req_wdata);
  localparam int unsigned CSR_PRIV_W = $bits(csr.req_priv);

  // --------------------------------------------------------------------------
  // Global CSRs / config
  // --------------------------------------------------------------------------
  logic cfg_enable_q;
  logic [7:0] cfg_default_mode_q;

  logic [15:0] csr_ctx_sel_q;
  logic [3:0]  csr_rf_index_q;

  logic [63:0] csr_comp_base_q;
  logic [31:0] csr_comp_mask_q;
  logic        csr_comp_irq_en_q;

  logic [31:0] legacy_ctrl_q;
  logic [31:0] legacy_push_lo_q;
  logic [31:0] legacy_push_hi_q;

  // --------------------------------------------------------------------------
  // Context file (single-ported, muxed between CAI and CSR/legacy)
  // --------------------------------------------------------------------------
  logic [15:0] ctx_sel_mux;
  logic [3:0]  rf_index_mux;

  logic [1:0]  rm_rdata;
  logic [4:0]  flags_rdata;
  logic [63:0] rf_rdata;

  logic [63:0] stack_top;
  logic        stack_empty;
  logic        stack_full;
  logic [$clog2(LEGACY_STACK_DEPTH+1)-1:0] stack_depth;
  logic [63:0] stack_pop_data;
  logic stack_overflow_pulse;
  logic stack_underflow_pulse;

  logic rm_we_mux;
  logic [1:0] rm_wdata_mux;
  logic flags_or_we_mux;
  logic [4:0] flags_or_mask_mux;
  logic flags_clr_we_mux;
  logic [4:0] flags_clr_mask_mux;
  logic rf_we_mux;
  logic [63:0] rf_wdata_mux;
  logic stack_push_we_mux;
  logic [63:0] stack_push_data_mux;
  logic stack_pop_we_mux;

  am9513_context_file #(
      .NUM_CONTEXTS(NUM_CONTEXTS),
      .LEGACY_STACK_DEPTH(LEGACY_STACK_DEPTH)
  ) u_ctx (
      .clk(clk),
      .rst_n(rst_n),
      .ctx_sel(ctx_sel_mux),
      .rf_index(rf_index_mux),
      .rm_rdata(rm_rdata),
      .flags_rdata(flags_rdata),
      .rf_rdata(rf_rdata),
      .stack_top_rdata(stack_top),
      .stack_empty(stack_empty),
      .stack_full(stack_full),
      .stack_depth(stack_depth),
      .rm_we(rm_we_mux),
      .rm_wdata(rm_wdata_mux),
      .flags_or_we(flags_or_we_mux),
      .flags_or_mask(flags_or_mask_mux),
      .flags_clr_we(flags_clr_we_mux),
      .flags_clr_mask(flags_clr_mask_mux),
      .rf_we(rf_we_mux),
      .rf_wdata(rf_wdata_mux),
      .stack_push_we(stack_push_we_mux),
      .stack_push_data(stack_push_data_mux),
      .stack_pop_we(stack_pop_we_mux),
      .stack_pop_data(stack_pop_data),
      .stack_overflow_pulse(stack_overflow_pulse),
      .stack_underflow_pulse(stack_underflow_pulse)
  );

  // --------------------------------------------------------------------------
  // Legacy shell (executes stack ops)
  // --------------------------------------------------------------------------
  logic legacy_start_pulse;
  logic [7:0] legacy_op_q;
  logic legacy_busy;
  logic [7:0] legacy_last_status;

  logic legacy_stack_pop_we;
  logic legacy_stack_push_we;
  logic [63:0] legacy_stack_push_data;
  logic legacy_flags_or_we;
  logic [4:0] legacy_flags_or_mask;

  am9513_legacy_shell #(
      .LEGACY_STACK_DEPTH(LEGACY_STACK_DEPTH)
  ) u_legacy (
      .clk(clk),
      .rst_n(rst_n),
      .start(legacy_start_pulse),
      .legacy_op(legacy_op_q),
      .legacy_ctrl(legacy_ctrl_q),
      .rm(rm_rdata),
      .stack_depth(stack_depth),
      .stack_empty(stack_empty),
      .stack_full(stack_full),
      .stack_top(stack_top),
      .stack_pop_we(legacy_stack_pop_we),
      .stack_push_we(legacy_stack_push_we),
      .stack_push_data(legacy_stack_push_data),
      .flags_or_we(legacy_flags_or_we),
      .flags_or_mask(legacy_flags_or_mask),
      .busy(legacy_busy),
      .last_status(legacy_last_status)
  );

  // --------------------------------------------------------------------------
  // CAI engine
  // --------------------------------------------------------------------------
  logic cai_busy;
  logic [15:0] cai_ctx_sel;
  logic [3:0]  cai_rf_index;
  logic cai_flags_or_we;
  logic [4:0] cai_flags_or_mask;
  logic cai_rf_we;
  logic [63:0] cai_rf_wdata;

  am9513_cai_engine #(
      .NUM_CONTEXTS(NUM_CONTEXTS),
      .MAX_OPERANDS(3),
      .PENDING_DEPTH(8)
  ) u_cai (
      .clk(clk),
      .rst_n(rst_n),
      .mem_if(mem_if),
      .cai(cai),
      .cfg_enable(cfg_enable_q && !legacy_busy),
      .cfg_default_mode(cfg_default_mode_q),
      .cfg_comp_base(csr_comp_base_q),
      .cfg_comp_ring_mask(csr_comp_mask_q),
      .cfg_comp_irq_en(csr_comp_irq_en_q),
      .ctx_sel(cai_ctx_sel),
      .rf_index(cai_rf_index),
      .rm_rdata(rm_rdata),
      .rf_rdata(rf_rdata),
      .flags_or_we(cai_flags_or_we),
      .flags_or_mask(cai_flags_or_mask),
      .rf_we(cai_rf_we),
      .rf_wdata(cai_rf_wdata),
      .busy(cai_busy)
  );

  // --------------------------------------------------------------------------
  // Context file muxing
  // --------------------------------------------------------------------------
  always_comb begin
    // Defaults: CSR/legacy owns the context port.
    ctx_sel_mux = csr_ctx_sel_q;
    rf_index_mux = csr_rf_index_q;

    rm_we_mux = csr_rm_we_pulse_q;
    rm_wdata_mux = csr_rm_wdata_q;

    flags_or_we_mux = legacy_flags_or_we;
    flags_or_mask_mux = legacy_flags_or_mask;

    flags_clr_we_mux = csr_flags_clr_pulse_q;
    flags_clr_mask_mux = csr_flags_clr_mask_q;

    rf_we_mux = csr_rf_we_pulse_q;
    rf_wdata_mux = csr_rf_wdata_q;

    stack_push_we_mux = csr_stack_push_pulse_q;
    stack_push_data_mux = csr_stack_push_data_q;
    stack_pop_we_mux = legacy_stack_pop_we | csr_stack_pop_pulse_q;

    if (legacy_stack_push_we) begin
      stack_push_we_mux = 1'b1;
      stack_push_data_mux = legacy_stack_push_data;
    end

    if (cai_busy) begin
      // CAI owns context port during CAI processing.
      ctx_sel_mux = cai_ctx_sel;
      rf_index_mux = cai_rf_index;
      flags_or_we_mux = cai_flags_or_we;
      flags_or_mask_mux = cai_flags_or_mask;
      rf_we_mux = cai_rf_we;
      rf_wdata_mux = cai_rf_wdata;
      stack_push_we_mux = 1'b0;
      stack_pop_we_mux = 1'b0;
      flags_clr_we_mux = 1'b0;
      rm_we_mux = 1'b0;
    end
  end

  // --------------------------------------------------------------------------
  // CSR interface
  // --------------------------------------------------------------------------
  logic csr_rsp_valid_q;
  logic [CSR_DATA_W-1:0] csr_rsp_rdata_q;
  logic csr_rsp_fault_q;
  logic csr_rsp_side_q;

  wire csr_rsp_fire = csr.rsp_valid && csr.rsp_ready;

  // Gate CSR acceptance when CAI is active. Allow LEGACY_STATUS polling while legacy busy.
  logic csr_allow_when_legacy_busy;
  always_comb begin
    csr_allow_when_legacy_busy =
        (csr.req_addr == CSR_ADDR_W'(CARBON_CSR_AM9513_LEGACY_STATUS)) ||
        (csr.req_addr == CSR_ADDR_W'(CARBON_CSR_AM9513_STATUS));
  end

  assign csr.req_ready = (!csr_rsp_valid_q) &&
                         (!cai_busy) &&
                         (!(legacy_busy) || csr_allow_when_legacy_busy);

  assign csr.rsp_valid = csr_rsp_valid_q;
  assign csr.rsp_rdata = csr_rsp_rdata_q;
  assign csr.rsp_fault = csr_rsp_fault_q;
  assign csr.rsp_side_effect = csr_rsp_side_q;

  wire csr_req_fire = csr.req_valid && csr.req_ready;

  // CSR-derived context write pulses (applied via mux when not CAI-owned).
  logic csr_rm_we_pulse_q;
  logic [1:0] csr_rm_wdata_q;
  logic csr_flags_clr_pulse_q;
  logic [4:0] csr_flags_clr_mask_q;
  logic csr_rf_we_pulse_q;
  logic [63:0] csr_rf_wdata_q;
  logic csr_stack_push_pulse_q;
  logic [63:0] csr_stack_push_data_q;
  logic csr_stack_pop_pulse_q;

  // Staged RF write
  logic [31:0] csr_rf_stage_lo_q;
  logic [31:0] csr_rf_stage_hi_q;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      cfg_enable_q <= 1'b0;
      cfg_default_mode_q <= AM9513_P0_AM9511;

      csr_ctx_sel_q <= '0;
      csr_rf_index_q <= '0;

      csr_comp_base_q <= '0;
      csr_comp_mask_q <= 32'h0000_00FF;
      csr_comp_irq_en_q <= 1'b0;

      legacy_ctrl_q <= 32'h0;
      legacy_push_lo_q <= '0;
      legacy_push_hi_q <= '0;
      legacy_op_q <= '0;
      legacy_start_pulse <= 1'b0;

      csr_rf_stage_lo_q <= '0;
      csr_rf_stage_hi_q <= '0;

      csr_rm_we_pulse_q <= 1'b0;
      csr_rm_wdata_q <= 2'(CARBON_RND_RN);
      csr_flags_clr_pulse_q <= 1'b0;
      csr_flags_clr_mask_q <= '0;
      csr_rf_we_pulse_q <= 1'b0;
      csr_rf_wdata_q <= '0;
      csr_stack_push_pulse_q <= 1'b0;
      csr_stack_push_data_q <= '0;
      csr_stack_pop_pulse_q <= 1'b0;

      csr_rsp_valid_q <= 1'b0;
      csr_rsp_rdata_q <= '0;
      csr_rsp_fault_q <= 1'b0;
      csr_rsp_side_q <= 1'b0;
    end else begin
      legacy_start_pulse <= 1'b0;

      csr_rm_we_pulse_q <= 1'b0;
      csr_flags_clr_pulse_q <= 1'b0;
      csr_rf_we_pulse_q <= 1'b0;
      csr_stack_push_pulse_q <= 1'b0;
      csr_stack_pop_pulse_q <= 1'b0;

      if (csr_rsp_fire) begin
        csr_rsp_valid_q <= 1'b0;
      end

      if (csr_req_fire) begin
        csr_rsp_valid_q <= 1'b1;
        csr_rsp_rdata_q <= '0;
        csr_rsp_fault_q <= 1'b0;
        csr_rsp_side_q <= 1'b0;

        unique case (csr.req_addr)
          CSR_ADDR_W'(CARBON_CSR_AM9513_ID): begin
            // [31:16] version, [15:0] feature bitmap (v1=0x0001)
            csr_rsp_rdata_q <= 32'h0001_9513;
          end

          CSR_ADDR_W'(CARBON_CSR_AM9513_CTRL): begin
            if (csr.req_write) begin
              cfg_enable_q <= csr.req_wdata[0];
            end else begin
              csr_rsp_rdata_q[0] <= cfg_enable_q;
            end
          end

          CSR_ADDR_W'(CARBON_CSR_AM9513_STATUS): begin
            csr_rsp_rdata_q[0] <= cfg_enable_q;
            csr_rsp_rdata_q[1] <= cai_busy;
            csr_rsp_rdata_q[2] <= legacy_busy;
            csr_rsp_rdata_q[15:8] <= cai.status[15:8];
            csr_rsp_rdata_q[31:16] <= 16'h0000;
          end

          CSR_ADDR_W'(CARBON_CSR_AM9513_MODE): begin
            if (csr.req_write) begin
              cfg_default_mode_q <= csr.req_wdata[7:0];
            end else begin
              csr_rsp_rdata_q[7:0] <= cfg_default_mode_q;
            end
          end

          CSR_ADDR_W'(CARBON_CSR_AM9513_CTX_SEL): begin
            if (csr.req_write) csr_ctx_sel_q <= csr.req_wdata[15:0];
            else csr_rsp_rdata_q[15:0] <= csr_ctx_sel_q;
          end

          CSR_ADDR_W'(CARBON_CSR_AM9513_CTX_RM): begin
            if (csr.req_write) begin
              csr_rm_we_pulse_q <= 1'b1;
              csr_rm_wdata_q <= csr.req_wdata[1:0];
            end else begin
              csr_rsp_rdata_q[1:0] <= rm_rdata;
            end
          end

          CSR_ADDR_W'(CARBON_CSR_AM9513_CTX_FLAGS): begin
            csr_rsp_rdata_q[4:0] <= flags_rdata;
          end

          CSR_ADDR_W'(CARBON_CSR_AM9513_CTX_FLAGS_CLR): begin
            if (csr.req_write) begin
              csr_flags_clr_pulse_q <= 1'b1;
              csr_flags_clr_mask_q <= csr.req_wdata[4:0];
            end
          end

          CSR_ADDR_W'(CARBON_CSR_AM9513_RF_INDEX): begin
            if (csr.req_write) csr_rf_index_q <= csr.req_wdata[3:0];
            else csr_rsp_rdata_q[3:0] <= csr_rf_index_q;
          end

          CSR_ADDR_W'(CARBON_CSR_AM9513_RF_DATA_LO): begin
            if (csr.req_write) begin
              csr_rf_stage_lo_q <= csr.req_wdata;
            end else begin
              csr_rsp_rdata_q <= rf_rdata[31:0];
            end
          end

          CSR_ADDR_W'(CARBON_CSR_AM9513_RF_DATA_HI): begin
            if (csr.req_write) begin
              csr_rf_stage_hi_q <= csr.req_wdata;
              csr_rf_we_pulse_q <= 1'b1;
              csr_rf_wdata_q <= {csr.req_wdata, csr_rf_stage_lo_q};
            end else begin
              csr_rsp_rdata_q <= rf_rdata[63:32];
            end
          end

          CSR_ADDR_W'(CARBON_CSR_AM9513_CAI_COMP_BASE_LO): begin
            if (csr.req_write) csr_comp_base_q[31:0] <= csr.req_wdata;
            else csr_rsp_rdata_q <= csr_comp_base_q[31:0];
          end
          CSR_ADDR_W'(CARBON_CSR_AM9513_CAI_COMP_BASE_HI): begin
            if (csr.req_write) csr_comp_base_q[63:32] <= csr.req_wdata;
            else csr_rsp_rdata_q <= csr_comp_base_q[63:32];
          end
          CSR_ADDR_W'(CARBON_CSR_AM9513_CAI_COMP_RING_MASK): begin
            if (csr.req_write) csr_comp_mask_q <= csr.req_wdata;
            else csr_rsp_rdata_q <= csr_comp_mask_q;
          end
          CSR_ADDR_W'(CARBON_CSR_AM9513_CAI_IRQ_ENABLE): begin
            if (csr.req_write) csr_comp_irq_en_q <= csr.req_wdata[0];
            else csr_rsp_rdata_q[0] <= csr_comp_irq_en_q;
          end

          CSR_ADDR_W'(CARBON_CSR_AM9513_LEGACY_CTRL): begin
            if (csr.req_write) legacy_ctrl_q <= csr.req_wdata;
            else csr_rsp_rdata_q <= legacy_ctrl_q;
          end

          CSR_ADDR_W'(CARBON_CSR_AM9513_LEGACY_STATUS): begin
            csr_rsp_rdata_q[0] <= legacy_busy;
            csr_rsp_rdata_q[7:4] <= 4'(stack_depth);
            csr_rsp_rdata_q[8] <= stack_empty;
            csr_rsp_rdata_q[9] <= stack_full;
            csr_rsp_rdata_q[15:8] <= legacy_last_status;
          end

          CSR_ADDR_W'(CARBON_CSR_AM9513_LEGACY_PUSH_LO): begin
            if (csr.req_write) legacy_push_lo_q <= csr.req_wdata;
          end

          CSR_ADDR_W'(CARBON_CSR_AM9513_LEGACY_PUSH_HI): begin
            if (csr.req_write) begin
              legacy_push_hi_q <= csr.req_wdata;
              csr_stack_push_pulse_q <= 1'b1;
              csr_stack_push_data_q <= {csr.req_wdata, legacy_push_lo_q};
            end
          end

          CSR_ADDR_W'(CARBON_CSR_AM9513_LEGACY_POP_LO): begin
            csr_rsp_rdata_q <= stack_top[31:0];
          end

          CSR_ADDR_W'(CARBON_CSR_AM9513_LEGACY_POP_HI): begin
            csr_rsp_rdata_q <= stack_top[63:32];
            csr_rsp_side_q <= 1'b1;
            csr_stack_pop_pulse_q <= 1'b1;
          end

          CSR_ADDR_W'(CARBON_CSR_AM9513_LEGACY_OP): begin
            if (csr.req_write) begin
              if (legacy_busy) begin
                csr_rsp_fault_q <= 1'b1;
              end else begin
                legacy_op_q <= csr.req_wdata[7:0];
                legacy_start_pulse <= 1'b1;
              end
            end
          end

          default: begin
            csr_rsp_fault_q <= 1'b1;
          end
        endcase
      end
    end
  end

endmodule : am9513_accel
