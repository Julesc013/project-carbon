// Project Carbon - CarbonDMA peripheral (v1.0)
// carbondma: Multi-channel DMA engine with compat + turbo personalities.

module carbondma #(
    parameter logic [31:0] COMPAT_BASE_ADDR = 32'h0000_0000,
    parameter int unsigned CHANNELS = carbondma_pkg::CARBONDMA_CHANNELS_DEFAULT,
    parameter int unsigned RESP_LATENCY = 1
) (
    input logic clk,
    input logic rst_n,

    fabric_if.slave compat_if,
    fabric_if.master mem_if,
    csr_if.slave    csr,
    dbg_if.core     dbg
);
  import carbon_arch_pkg::*;
  import carbondma_pkg::*;

  localparam int unsigned MEM_ADDR_W = $bits(mem_if.req_addr);
  localparam int unsigned MEM_DATA_W = $bits(mem_if.req_wdata);
  localparam int unsigned MEM_STRB_W = $bits(mem_if.req_wstrb);
  localparam int unsigned MEM_ATTR_W = $bits(mem_if.req_attr);
  localparam int unsigned MEM_OP_W   = $bits(mem_if.req_op);
  localparam int unsigned MEM_CODE_W = $bits(mem_if.rsp_code);
  localparam int unsigned COMPAT_DATA_W = $bits(compat_if.req_wdata);
  localparam int unsigned COMPAT_CODE_W = $bits(compat_if.rsp_code);
  localparam int unsigned COMPAT_OP_W   = $bits(compat_if.req_op);
  localparam int unsigned COMPAT_ID_W   = $bits(compat_if.req_id);
  localparam int unsigned CH_W = (CHANNELS <= 1) ? 1 : $clog2(CHANNELS);

  localparam logic [15:0] CARBONDMA_DEVICE_ID  = 16'h0001;
  localparam logic [15:0] CARBONDMA_DEVICE_VER = 16'h0001;

  // --------------------------------------------------------------------------
  // Debug gating (halt/step)
  // --------------------------------------------------------------------------
  logic dbg_halt_q;
  logic dbg_step_pulse_q;
  logic dbg_step_ack_q;

  wire dbg_halt_req = dbg.halt_req;
  wire dbg_run_req  = dbg.run_req;
  wire dbg_step_req = dbg.step_req;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      dbg_halt_q <= 1'b0;
      dbg_step_pulse_q <= 1'b0;
      dbg_step_ack_q <= 1'b0;
    end else begin
      dbg_step_pulse_q <= 1'b0;
      dbg_step_ack_q <= 1'b0;
      if (dbg_run_req) dbg_halt_q <= 1'b0;
      if (dbg_halt_req) dbg_halt_q <= 1'b1;
      if (dbg_step_req && dbg_halt_q) begin
        dbg_step_pulse_q <= 1'b1;
        dbg_step_ack_q <= 1'b1;
      end
    end
  end

  assign dbg.halt_ack = dbg_halt_q;
  assign dbg.step_ack = dbg_step_ack_q;
  assign dbg.bp_ready = 1'b0;
  assign dbg.trace_valid = 1'b0;
  assign dbg.trace_data = '0;

  wire run_enable = !dbg_halt_q || dbg_step_pulse_q;

  // --------------------------------------------------------------------------
  // Helpers
  // --------------------------------------------------------------------------
  function automatic logic [31:0] pack_field(
      input int unsigned value,
      input int unsigned lsb,
      input int unsigned width
  );
    logic [31:0] v;
    begin
      if (width >= 32) v = value[31:0];
      else v = value[width-1:0];
      pack_field = v << lsb;
    end
  endfunction

  function automatic logic [31:0] apply_wstrb(
      input logic [31:0] orig,
      input logic [31:0] wdata,
      input logic [3:0] wstrb
  );
    logic [31:0] v;
    begin
      v = orig;
      if (wstrb[0]) v[7:0]   = wdata[7:0];
      if (wstrb[1]) v[15:8]  = wdata[15:8];
      if (wstrb[2]) v[23:16] = wdata[23:16];
      if (wstrb[3]) v[31:24] = wdata[31:24];
      apply_wstrb = v;
    end
  endfunction

  // --------------------------------------------------------------------------
  // Feature words
  // --------------------------------------------------------------------------
  logic [31:0] feature_word0;
  logic [31:0] feature_word1;

  always_comb begin
    feature_word0 = 32'h0;
    feature_word1 = 32'h0;
    feature_word0 |= pack_field(CHANNELS, CARBON_DEVFEAT_FIELD_DMA_CHANNELS_LSB,
                                CARBON_DEVFEAT_FIELD_DMA_CHANNELS_WIDTH);
    feature_word1 |= pack_field(1, CARBON_DEVFEAT_FIELD_QUEUE_COUNT_LSB,
                                CARBON_DEVFEAT_FIELD_QUEUE_COUNT_WIDTH);
  end

  // --------------------------------------------------------------------------
  // Global registers
  // --------------------------------------------------------------------------
  logic cfg_enable_q;
  logic [31:0] cfg_mode_q;

  logic [63:0] queue_submit_base_q;
  logic [31:0] queue_submit_mask_q;
  logic [63:0] queue_comp_base_q;
  logic [31:0] queue_comp_mask_q;
  logic [31:0] queue_submit_head_q;
  logic [31:0] queue_submit_tail_q;
  logic [31:0] queue_comp_head_q;
  logic queue_comp_doorbell_q;
  logic queue_error_q;

  logic [CH_W-1:0] ch_sel_q;
  logic [CHANNELS-1:0][63:0] ch_src_q;
  logic [CHANNELS-1:0][63:0] ch_dst_q;
  logic [CHANNELS-1:0][31:0] ch_len_q;
  logic [CHANNELS-1:0][31:0] ch_ctrl_q;
  logic [CHANNELS-1:0][31:0] ch_attr_q;
  logic [CHANNELS-1:0][31:0] ch_fill_q;
  logic [CHANNELS-1:0] ch_pending_q;
  logic [CHANNELS-1:0] ch_busy_q;
  logic [CHANNELS-1:0] ch_done_q;
  logic [CHANNELS-1:0] ch_err_q;

  // --------------------------------------------------------------------------
  // Queue + DMA state
  // --------------------------------------------------------------------------
  typedef enum logic [3:0] {
    ST_IDLE,
    ST_FETCH_SUBMIT_REQ,
    ST_FETCH_SUBMIT_RESP,
    ST_PARSE_SUBMIT,
    ST_FETCH_ENTRY_REQ,
    ST_FETCH_ENTRY_RESP,
    ST_PARSE_ENTRY,
    ST_DMA_READ_REQ,
    ST_DMA_READ_RESP,
    ST_DMA_WRITE_REQ,
    ST_DMA_WRITE_RESP,
    ST_COMP_WRITE_REQ,
    ST_COMP_WRITE_RESP
  } dma_state_e;

  dma_state_e state_q;
  logic [2:0] mem_word_index_q;

  logic [31:0] submit_words [0:7];
  logic [31:0] entry_words  [0:7];
  logic [31:0] comp_words   [0:3];

  logic [31:0] queue_tag_q;
  logic [15:0] queue_opcode_q;
  logic [31:0] queue_flags_q;
  logic [63:0] queue_data_ptr_q;
  logic [31:0] queue_data_len_q;
  logic [31:0] queue_data_stride_q;
  logic [31:0] queue_entry_count_q;
  logic [31:0] queue_entry_index_q;
  logic [31:0] queue_entry_stride_q;
  logic [31:0] queue_bytes_done_q;
  logic [15:0] queue_status_code_q;

  logic cmd_from_queue_q;
  logic [CH_W-1:0] cmd_channel_q;
  logic [63:0] cmd_src_q;
  logic [63:0] cmd_dst_q;
  logic [31:0] cmd_len_q;
  logic [31:0] cmd_remaining_q;
  logic cmd_fill_q;
  logic [31:0] cmd_fill_data_q;
  logic [MEM_ATTR_W-1:0] cmd_attr_src_q;
  logic [MEM_ATTR_W-1:0] cmd_attr_dst_q;
  logic cmd_error_q;
  logic [7:0] read_byte_q;

  // --------------------------------------------------------------------------
  // CSR interface (single outstanding response)
  // --------------------------------------------------------------------------
  logic csr_rsp_valid_q;
  logic [31:0] csr_rsp_rdata_q;
  logic csr_rsp_fault_q;
  logic csr_rsp_side_q;

  assign csr.req_ready = !csr_rsp_valid_q;
  assign csr.rsp_valid = csr_rsp_valid_q;
  assign csr.rsp_rdata = csr_rsp_rdata_q;
  assign csr.rsp_fault = csr_rsp_fault_q;
  assign csr.rsp_side_effect = csr_rsp_side_q;

  wire csr_req_fire = csr.req_valid && csr.req_ready;
  wire csr_rsp_fire = csr.rsp_valid && csr.rsp_ready;

  // --------------------------------------------------------------------------
  // Compatibility (fabric) interface
  // --------------------------------------------------------------------------
  logic compat_rsp_valid_q;
  logic [COMPAT_DATA_W-1:0] compat_rsp_rdata_q;
  logic [COMPAT_CODE_W-1:0] compat_rsp_code_q;
  logic [COMPAT_ID_W-1:0] compat_rsp_id_q;
  logic compat_busy_q;
  logic [31:0] compat_delay_q;

  assign compat_if.req_ready = !compat_busy_q;
  assign compat_if.rsp_valid = compat_rsp_valid_q;
  assign compat_if.rsp_rdata = compat_rsp_rdata_q;
  assign compat_if.rsp_code  = compat_rsp_code_q;
  assign compat_if.rsp_id    = compat_rsp_id_q;

  wire compat_req_fire = compat_if.req_valid && compat_if.req_ready;
  wire compat_rsp_fire = compat_if.rsp_valid && compat_if.rsp_ready;

  // --------------------------------------------------------------------------
  // Fabric master (mem_if) control
  // --------------------------------------------------------------------------
  wire mem_req_fire = mem_if.req_valid && mem_if.req_ready;
  wire mem_rsp_fire = mem_if.rsp_valid && mem_if.rsp_ready;

  assign mem_if.rsp_ready = 1'b1;

  logic [7:0] fill_byte;
  logic [7:0] write_byte;
  assign fill_byte = cmd_fill_data_q >> (cmd_dst_q[1:0] * 8);
  assign write_byte = cmd_fill_q ? fill_byte : read_byte_q;

  // Combinational selection of pending channel.
  logic pending_any;
  logic [CH_W-1:0] pending_idx;
  integer i;
  always_comb begin
    pending_any = 1'b0;
    pending_idx = '0;
    for (i = 0; i < CHANNELS; i++) begin
      if (!pending_any && ch_pending_q[i]) begin
        pending_any = 1'b1;
        pending_idx = CH_W'(i);
      end
    end
  end

  wire queue_active = (queue_submit_head_q != queue_submit_tail_q) &&
                      cfg_enable_q && run_enable && cfg_mode_q[0];

  // --------------------------------------------------------------------------
  // mem_if request mux (combinational)
  // --------------------------------------------------------------------------
  always_comb begin
    mem_if.req_valid = 1'b0;
    mem_if.req_op    = MEM_OP_W'(CARBON_FABRIC_XACT_READ);
    mem_if.req_addr  = '0;
    mem_if.req_wdata = '0;
    mem_if.req_wstrb = '0;
    mem_if.req_size  = 3'(2);
    mem_if.req_attr  = '0;
    mem_if.req_id    = '0;

    unique case (state_q)
      ST_FETCH_SUBMIT_REQ: begin
        mem_if.req_valid = 1'b1;
        mem_if.req_op    = MEM_OP_W'(CARBON_FABRIC_XACT_READ);
        mem_if.req_addr  = MEM_ADDR_W'(queue_submit_base_q[31:0] +
                         ((queue_submit_head_q & queue_submit_mask_q) << 5) +
                         (mem_word_index_q << 2));
        mem_if.req_size  = 3'(2);
        mem_if.req_attr  = '0;
      end
      ST_FETCH_ENTRY_REQ: begin
        mem_if.req_valid = 1'b1;
        mem_if.req_op    = MEM_OP_W'(CARBON_FABRIC_XACT_READ);
        mem_if.req_addr  = MEM_ADDR_W'(queue_data_ptr_q[31:0] +
                         (queue_entry_index_q * queue_entry_stride_q) +
                         (mem_word_index_q << 2));
        mem_if.req_size  = 3'(2);
        mem_if.req_attr  = '0;
      end
      ST_DMA_READ_REQ: begin
        if (!cmd_fill_q) begin
          mem_if.req_valid = 1'b1;
          mem_if.req_op    = MEM_OP_W'(CARBON_FABRIC_XACT_READ);
          mem_if.req_addr  = MEM_ADDR_W'(cmd_src_q[31:0]);
          mem_if.req_size  = 3'(0);
          mem_if.req_attr  = cmd_attr_src_q;
        end
      end
      ST_DMA_WRITE_REQ: begin
        mem_if.req_valid = 1'b1;
        mem_if.req_op    = MEM_OP_W'(CARBON_FABRIC_XACT_WRITE);
        mem_if.req_addr  = MEM_ADDR_W'(cmd_dst_q[31:0]);
        mem_if.req_wdata = MEM_DATA_W'({24'h0, write_byte});
        mem_if.req_wstrb = MEM_STRB_W'(4'b0001);
        mem_if.req_size  = 3'(0);
        mem_if.req_attr  = cmd_attr_dst_q;
      end
      ST_COMP_WRITE_REQ: begin
        mem_if.req_valid = 1'b1;
        mem_if.req_op    = MEM_OP_W'(CARBON_FABRIC_XACT_WRITE);
        mem_if.req_addr  = MEM_ADDR_W'(queue_comp_base_q[31:0] +
                         ((queue_comp_head_q & queue_comp_mask_q) << 4) +
                         (mem_word_index_q << 2));
        mem_if.req_wdata = MEM_DATA_W'(comp_words[mem_word_index_q]);
        mem_if.req_wstrb = MEM_STRB_W'({MEM_STRB_W{1'b1}});
        mem_if.req_size  = 3'(2);
        mem_if.req_attr  = '0;
      end
      default: begin
      end
    endcase
  end

  // --------------------------------------------------------------------------
  // Main state machine and register updates
  // --------------------------------------------------------------------------
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      cfg_enable_q <= 1'b1;
      cfg_mode_q <= 32'h0;

      queue_submit_base_q <= 64'h0;
      queue_submit_mask_q <= 32'h0;
      queue_comp_base_q <= 64'h0;
      queue_comp_mask_q <= 32'h0;
      queue_submit_head_q <= 32'h0;
      queue_submit_tail_q <= 32'h0;
      queue_comp_head_q <= 32'h0;
      queue_comp_doorbell_q <= 1'b0;
      queue_error_q <= 1'b0;

      ch_sel_q <= '0;
      ch_src_q <= '0;
      ch_dst_q <= '0;
      ch_len_q <= '0;
      ch_ctrl_q <= '0;
      ch_attr_q <= '0;
      ch_fill_q <= '0;
      ch_pending_q <= '0;
      ch_busy_q <= '0;
      ch_done_q <= '0;
      ch_err_q <= '0;

      state_q <= ST_IDLE;
      mem_word_index_q <= 3'h0;

      queue_tag_q <= 32'h0;
      queue_opcode_q <= 16'h0;
      queue_flags_q <= 32'h0;
      queue_data_ptr_q <= 64'h0;
      queue_data_len_q <= 32'h0;
      queue_data_stride_q <= 32'h0;
      queue_entry_count_q <= 32'h0;
      queue_entry_index_q <= 32'h0;
      queue_entry_stride_q <= 32'h0;
      queue_bytes_done_q <= 32'h0;
      queue_status_code_q <= 16'(CARBONDMA_TURBO_STATUS_OK);

      cmd_from_queue_q <= 1'b0;
      cmd_channel_q <= '0;
      cmd_src_q <= 64'h0;
      cmd_dst_q <= 64'h0;
      cmd_len_q <= 32'h0;
      cmd_remaining_q <= 32'h0;
      cmd_fill_q <= 1'b0;
      cmd_fill_data_q <= 32'h0;
      cmd_attr_src_q <= '0;
      cmd_attr_dst_q <= '0;
      cmd_error_q <= 1'b0;
      read_byte_q <= 8'h0;

      csr_rsp_valid_q <= 1'b0;
      csr_rsp_rdata_q <= 32'h0;
      csr_rsp_fault_q <= 1'b0;
      csr_rsp_side_q <= 1'b0;

      compat_rsp_valid_q <= 1'b0;
      compat_rsp_rdata_q <= '0;
      compat_rsp_code_q <= '0;
      compat_rsp_id_q <= '0;
      compat_busy_q <= 1'b0;
      compat_delay_q <= '0;
    end else begin
      csr_rsp_side_q <= 1'b0;
      csr_rsp_fault_q <= 1'b0;

      if (csr_rsp_fire) begin
        csr_rsp_valid_q <= 1'b0;
      end

      if (compat_rsp_fire) begin
        compat_rsp_valid_q <= 1'b0;
        compat_busy_q <= 1'b0;
      end

      if (compat_busy_q && !compat_rsp_valid_q) begin
        if (compat_delay_q != 0) begin
          compat_delay_q <= compat_delay_q - 1'b1;
        end else begin
          compat_rsp_valid_q <= 1'b1;
        end
      end

      // ------------------------------------------------------------------
      // Compat write side effects (CSR has priority later in this block)
      // ------------------------------------------------------------------
      if (compat_req_fire && compat_if.req_op == COMPAT_OP_W'(CARBON_FABRIC_XACT_WRITE)) begin
        logic [31:0] compat_addr_off;
        compat_addr_off = compat_if.req_addr - COMPAT_BASE_ADDR;
        unique case (compat_addr_off & 32'hFFFF_FFFC)
          CARBONDMA_COMPAT_CTRL_OFF: begin
            cfg_enable_q <= compat_if.req_wdata[CARBONDMA_CTRL_ENABLE_BIT];
            if (compat_if.req_wdata[CARBONDMA_CTRL_CLR_ERR_BIT]) begin
              ch_err_q <= '0;
              ch_done_q <= '0;
              queue_error_q <= 1'b0;
            end
          end
          CARBONDMA_COMPAT_CH_SEL_OFF: begin
            ch_sel_q <= compat_if.req_wdata[CH_W-1:0];
          end
          CARBONDMA_COMPAT_CH_SRC_LO_OFF: begin
            ch_src_q[ch_sel_q][31:0] <= apply_wstrb(ch_src_q[ch_sel_q][31:0],
                                                    compat_if.req_wdata, compat_if.req_wstrb);
          end
          CARBONDMA_COMPAT_CH_SRC_HI_OFF: begin
            ch_src_q[ch_sel_q][63:32] <= apply_wstrb(ch_src_q[ch_sel_q][63:32],
                                                     compat_if.req_wdata, compat_if.req_wstrb);
          end
          CARBONDMA_COMPAT_CH_DST_LO_OFF: begin
            ch_dst_q[ch_sel_q][31:0] <= apply_wstrb(ch_dst_q[ch_sel_q][31:0],
                                                    compat_if.req_wdata, compat_if.req_wstrb);
          end
          CARBONDMA_COMPAT_CH_DST_HI_OFF: begin
            ch_dst_q[ch_sel_q][63:32] <= apply_wstrb(ch_dst_q[ch_sel_q][63:32],
                                                     compat_if.req_wdata, compat_if.req_wstrb);
          end
          CARBONDMA_COMPAT_CH_LEN_OFF: begin
            ch_len_q[ch_sel_q] <= apply_wstrb(ch_len_q[ch_sel_q],
                                              compat_if.req_wdata, compat_if.req_wstrb);
          end
          CARBONDMA_COMPAT_CH_CTRL_OFF: begin
            logic [31:0] new_ctrl;
            new_ctrl = apply_wstrb(ch_ctrl_q[ch_sel_q], compat_if.req_wdata, compat_if.req_wstrb);
            ch_ctrl_q[ch_sel_q] <= new_ctrl & ~(32'(1) << CARBONDMA_CH_CTRL_START_BIT);
            if (new_ctrl[CARBONDMA_CH_CTRL_START_BIT]) begin
              ch_pending_q[ch_sel_q] <= 1'b1;
              ch_done_q[ch_sel_q] <= 1'b0;
              ch_err_q[ch_sel_q] <= 1'b0;
            end
          end
          CARBONDMA_COMPAT_CH_STATUS_OFF: begin
            ch_done_q[ch_sel_q] <= 1'b0;
            ch_err_q[ch_sel_q] <= 1'b0;
          end
          CARBONDMA_COMPAT_CH_ATTR_OFF: begin
            ch_attr_q[ch_sel_q] <= apply_wstrb(ch_attr_q[ch_sel_q],
                                               compat_if.req_wdata, compat_if.req_wstrb);
          end
          CARBONDMA_COMPAT_CH_FILL_OFF: begin
            ch_fill_q[ch_sel_q] <= apply_wstrb(ch_fill_q[ch_sel_q],
                                               compat_if.req_wdata, compat_if.req_wstrb);
          end
          default: begin
          end
        endcase
      end

      // ------------------------------------------------------------------
      // CSR register access
      // ------------------------------------------------------------------
      if (csr_req_fire) begin
        csr_rsp_valid_q <= 1'b1;
        csr_rsp_rdata_q <= 32'h0;
        csr_rsp_fault_q <= 1'b0;
        csr_rsp_side_q <= csr.req_write;

        unique case (csr.req_addr)
          CARBON_CSR_CARBONDMA_ID: begin
            if (!csr.req_write) csr_rsp_rdata_q <= {CARBONDMA_DEVICE_VER, CARBONDMA_DEVICE_ID};
            else csr_rsp_fault_q <= 1'b1;
          end
          CARBON_CSR_CARBONDMA_STATUS: begin
            csr_rsp_rdata_q[CARBONDMA_STATUS_BUSY_BIT] <= (state_q != ST_IDLE) || (|ch_busy_q);
            csr_rsp_rdata_q[CARBONDMA_STATUS_ERR_BIT] <= (|ch_err_q) || queue_error_q;
          end
          CARBON_CSR_CARBONDMA_CTRL: begin
            if (csr.req_write) begin
              cfg_enable_q <= csr.req_wdata[CARBONDMA_CTRL_ENABLE_BIT];
              if (csr.req_wdata[CARBONDMA_CTRL_CLR_ERR_BIT]) begin
                ch_err_q <= '0;
                ch_done_q <= '0;
                queue_error_q <= 1'b0;
              end
            end else begin
              csr_rsp_rdata_q[CARBONDMA_CTRL_ENABLE_BIT] <= cfg_enable_q;
            end
          end
          CARBON_CSR_CARBONDMA_MODE: begin
            if (csr.req_write) cfg_mode_q <= csr.req_wdata;
            else csr_rsp_rdata_q <= cfg_mode_q;
          end
          CARBON_CSR_CARBONDMA_FEATURE0: begin
            if (!csr.req_write) csr_rsp_rdata_q <= feature_word0;
            else csr_rsp_fault_q <= 1'b1;
          end
          CARBON_CSR_CARBONDMA_FEATURE1: begin
            if (!csr.req_write) csr_rsp_rdata_q <= feature_word1;
            else csr_rsp_fault_q <= 1'b1;
          end
          CARBON_CSR_CARBONDMA_QUEUE_SUBMIT_BASE_LO: begin
            if (csr.req_write) queue_submit_base_q[31:0] <= csr.req_wdata;
            else csr_rsp_rdata_q <= queue_submit_base_q[31:0];
          end
          CARBON_CSR_CARBONDMA_QUEUE_SUBMIT_BASE_HI: begin
            if (csr.req_write) queue_submit_base_q[63:32] <= csr.req_wdata;
            else csr_rsp_rdata_q <= queue_submit_base_q[63:32];
          end
          CARBON_CSR_CARBONDMA_QUEUE_SUBMIT_MASK: begin
            if (csr.req_write) queue_submit_mask_q <= csr.req_wdata;
            else csr_rsp_rdata_q <= queue_submit_mask_q;
          end
          CARBON_CSR_CARBONDMA_QUEUE_DOORBELL: begin
            if (csr.req_write) queue_submit_tail_q <= csr.req_wdata;
            else csr_rsp_fault_q <= 1'b1;
          end
          CARBON_CSR_CARBONDMA_QUEUE_COMP_BASE_LO: begin
            if (csr.req_write) queue_comp_base_q[31:0] <= csr.req_wdata;
            else csr_rsp_rdata_q <= queue_comp_base_q[31:0];
          end
          CARBON_CSR_CARBONDMA_QUEUE_COMP_BASE_HI: begin
            if (csr.req_write) queue_comp_base_q[63:32] <= csr.req_wdata;
            else csr_rsp_rdata_q <= queue_comp_base_q[63:32];
          end
          CARBON_CSR_CARBONDMA_QUEUE_COMP_MASK: begin
            if (csr.req_write) queue_comp_mask_q <= csr.req_wdata;
            else csr_rsp_rdata_q <= queue_comp_mask_q;
          end
          CARBON_CSR_CARBONDMA_QUEUE_COMP_DOORBELL: begin
            csr_rsp_rdata_q[0] <= queue_comp_doorbell_q;
            if (!csr.req_write) queue_comp_doorbell_q <= 1'b0;
          end
          CARBON_CSR_CARBONDMA_QUEUE_STATUS: begin
            csr_rsp_rdata_q[15:0] <= queue_submit_head_q[15:0];
            csr_rsp_rdata_q[31:16] <= queue_submit_tail_q[15:0];
          end
          CARBON_CSR_CARBONDMA_CH_SEL: begin
            if (csr.req_write) ch_sel_q <= csr.req_wdata[CH_W-1:0];
            else csr_rsp_rdata_q <= ch_sel_q;
          end
          CARBON_CSR_CARBONDMA_CH_SRC_LO: begin
            if (csr.req_write) ch_src_q[ch_sel_q][31:0] <= csr.req_wdata;
            else csr_rsp_rdata_q <= ch_src_q[ch_sel_q][31:0];
          end
          CARBON_CSR_CARBONDMA_CH_SRC_HI: begin
            if (csr.req_write) ch_src_q[ch_sel_q][63:32] <= csr.req_wdata;
            else csr_rsp_rdata_q <= ch_src_q[ch_sel_q][63:32];
          end
          CARBON_CSR_CARBONDMA_CH_DST_LO: begin
            if (csr.req_write) ch_dst_q[ch_sel_q][31:0] <= csr.req_wdata;
            else csr_rsp_rdata_q <= ch_dst_q[ch_sel_q][31:0];
          end
          CARBON_CSR_CARBONDMA_CH_DST_HI: begin
            if (csr.req_write) ch_dst_q[ch_sel_q][63:32] <= csr.req_wdata;
            else csr_rsp_rdata_q <= ch_dst_q[ch_sel_q][63:32];
          end
          CARBON_CSR_CARBONDMA_CH_LEN: begin
            if (csr.req_write) ch_len_q[ch_sel_q] <= csr.req_wdata;
            else csr_rsp_rdata_q <= ch_len_q[ch_sel_q];
          end
          CARBON_CSR_CARBONDMA_CH_CTRL: begin
            if (csr.req_write) begin
              ch_ctrl_q[ch_sel_q] <= csr.req_wdata & ~(32'(1) << CARBONDMA_CH_CTRL_START_BIT);
              if (csr.req_wdata[CARBONDMA_CH_CTRL_START_BIT]) begin
                ch_pending_q[ch_sel_q] <= 1'b1;
                ch_done_q[ch_sel_q] <= 1'b0;
                ch_err_q[ch_sel_q] <= 1'b0;
              end
            end else begin
              csr_rsp_rdata_q <= ch_ctrl_q[ch_sel_q];
            end
          end
          CARBON_CSR_CARBONDMA_CH_STATUS: begin
            csr_rsp_rdata_q[CARBONDMA_CH_STATUS_BUSY_BIT] <= ch_busy_q[ch_sel_q];
            csr_rsp_rdata_q[CARBONDMA_CH_STATUS_DONE_BIT] <= ch_done_q[ch_sel_q];
            csr_rsp_rdata_q[CARBONDMA_CH_STATUS_ERR_BIT]  <= ch_err_q[ch_sel_q];
            if (csr.req_write) begin
              ch_done_q[ch_sel_q] <= 1'b0;
              ch_err_q[ch_sel_q] <= 1'b0;
            end
          end
          CARBON_CSR_CARBONDMA_CH_ATTR: begin
            if (csr.req_write) ch_attr_q[ch_sel_q] <= csr.req_wdata;
            else csr_rsp_rdata_q <= ch_attr_q[ch_sel_q];
          end
          CARBON_CSR_CARBONDMA_CH_FILL: begin
            if (csr.req_write) ch_fill_q[ch_sel_q] <= csr.req_wdata;
            else csr_rsp_rdata_q <= ch_fill_q[ch_sel_q];
          end
          default: begin
            csr_rsp_fault_q <= 1'b1;
          end
        endcase
      end

      // ------------------------------------------------------------------
      // Compat response generation
      // ------------------------------------------------------------------
      if (compat_req_fire) begin
        compat_busy_q <= 1'b1;
        compat_delay_q <= RESP_LATENCY;
        compat_rsp_id_q <= compat_if.req_id;
        compat_rsp_rdata_q <= '0;
        compat_rsp_code_q <= COMPAT_CODE_W'(CARBON_FABRIC_RESP_OK);

        if (compat_if.req_op == COMPAT_OP_W'(CARBON_FABRIC_XACT_READ)) begin
          logic [31:0] addr_off;
          addr_off = compat_if.req_addr - COMPAT_BASE_ADDR;
          unique case (addr_off & 32'hFFFF_FFFC)
            CARBONDMA_COMPAT_ID_OFF: begin
              compat_rsp_rdata_q <= {CARBONDMA_DEVICE_VER, CARBONDMA_DEVICE_ID};
            end
            CARBONDMA_COMPAT_STATUS_OFF: begin
              compat_rsp_rdata_q[CARBONDMA_STATUS_BUSY_BIT] <= (state_q != ST_IDLE) || (|ch_busy_q);
              compat_rsp_rdata_q[CARBONDMA_STATUS_ERR_BIT] <= (|ch_err_q) || queue_error_q;
            end
            CARBONDMA_COMPAT_CTRL_OFF: begin
              compat_rsp_rdata_q[CARBONDMA_CTRL_ENABLE_BIT] <= cfg_enable_q;
            end
            CARBONDMA_COMPAT_CH_SEL_OFF: begin
              compat_rsp_rdata_q <= ch_sel_q;
            end
            CARBONDMA_COMPAT_CH_SRC_LO_OFF: begin
              compat_rsp_rdata_q <= ch_src_q[ch_sel_q][31:0];
            end
            CARBONDMA_COMPAT_CH_SRC_HI_OFF: begin
              compat_rsp_rdata_q <= ch_src_q[ch_sel_q][63:32];
            end
            CARBONDMA_COMPAT_CH_DST_LO_OFF: begin
              compat_rsp_rdata_q <= ch_dst_q[ch_sel_q][31:0];
            end
            CARBONDMA_COMPAT_CH_DST_HI_OFF: begin
              compat_rsp_rdata_q <= ch_dst_q[ch_sel_q][63:32];
            end
            CARBONDMA_COMPAT_CH_LEN_OFF: begin
              compat_rsp_rdata_q <= ch_len_q[ch_sel_q];
            end
            CARBONDMA_COMPAT_CH_CTRL_OFF: begin
              compat_rsp_rdata_q <= ch_ctrl_q[ch_sel_q];
            end
            CARBONDMA_COMPAT_CH_STATUS_OFF: begin
              compat_rsp_rdata_q[CARBONDMA_CH_STATUS_BUSY_BIT] <= ch_busy_q[ch_sel_q];
              compat_rsp_rdata_q[CARBONDMA_CH_STATUS_DONE_BIT] <= ch_done_q[ch_sel_q];
              compat_rsp_rdata_q[CARBONDMA_CH_STATUS_ERR_BIT]  <= ch_err_q[ch_sel_q];
            end
            CARBONDMA_COMPAT_CH_ATTR_OFF: begin
              compat_rsp_rdata_q <= ch_attr_q[ch_sel_q];
            end
            CARBONDMA_COMPAT_CH_FILL_OFF: begin
              compat_rsp_rdata_q <= ch_fill_q[ch_sel_q];
            end
            default: begin
              compat_rsp_code_q <= COMPAT_CODE_W'(CARBON_FABRIC_RESP_ACCESS_FAULT);
            end
          endcase
        end else if (compat_if.req_op != COMPAT_OP_W'(CARBON_FABRIC_XACT_WRITE)) begin
          compat_rsp_code_q <= COMPAT_CODE_W'(CARBON_FABRIC_RESP_ACCESS_FAULT);
        end
      end

      // ------------------------------------------------------------------
      // DMA state machine
      // ------------------------------------------------------------------
      case (state_q)
        ST_IDLE: begin
          if (queue_active) begin
            mem_word_index_q <= 3'h0;
            state_q <= ST_FETCH_SUBMIT_REQ;
          end else if (pending_any && cfg_enable_q && run_enable) begin
            cmd_from_queue_q <= 1'b0;
            cmd_channel_q <= pending_idx;
            cmd_src_q <= ch_src_q[pending_idx];
            cmd_dst_q <= ch_dst_q[pending_idx];
            cmd_len_q <= ch_len_q[pending_idx];
            cmd_remaining_q <= ch_len_q[pending_idx];
            cmd_fill_q <= ch_ctrl_q[pending_idx][CARBONDMA_CH_CTRL_FILL_BIT];
            cmd_fill_data_q <= ch_fill_q[pending_idx];
            cmd_attr_src_q <= ch_attr_q[pending_idx][MEM_ATTR_W-1:0];
            cmd_attr_dst_q <= ch_attr_q[pending_idx][(2*MEM_ATTR_W)-1:MEM_ATTR_W];
            cmd_error_q <= 1'b0;
            ch_pending_q[pending_idx] <= 1'b0;
            ch_busy_q[pending_idx] <= 1'b1;
            ch_done_q[pending_idx] <= 1'b0;
            ch_err_q[pending_idx] <= 1'b0;
            state_q <= cmd_fill_q ? ST_DMA_WRITE_REQ : ST_DMA_READ_REQ;
          end
        end
        ST_FETCH_SUBMIT_REQ: begin
          if (mem_req_fire) begin
            state_q <= ST_FETCH_SUBMIT_RESP;
          end
        end
        ST_FETCH_SUBMIT_RESP: begin
          if (mem_rsp_fire) begin
            if (mem_if.rsp_code != MEM_CODE_W'(CARBON_FABRIC_RESP_OK)) begin
              queue_status_code_q <= 16'(CARBONDMA_TURBO_STATUS_FAULT);
              queue_error_q <= 1'b1;
              mem_word_index_q <= 3'h0;
              comp_words[0] <= queue_tag_q;
              comp_words[1] <= {16'h0, 16'(CARBONDMA_TURBO_STATUS_FAULT)};
              comp_words[2] <= queue_bytes_done_q;
              comp_words[3] <= 32'h0;
              state_q <= ST_COMP_WRITE_REQ;
            end else begin
              submit_words[mem_word_index_q] <= mem_if.rsp_rdata;
              if (mem_word_index_q == 3'h7) begin
                state_q <= ST_PARSE_SUBMIT;
              end else begin
                mem_word_index_q <= mem_word_index_q + 1'b1;
                state_q <= ST_FETCH_SUBMIT_REQ;
              end
            end
          end
        end
        ST_PARSE_SUBMIT: begin
          logic [15:0] desc_version;
          logic [15:0] desc_size_dw;
          logic [15:0] desc_queue_id;
          logic [15:0] desc_opcode;
          logic [31:0] desc_flags;
          logic [31:0] desc_tag;
          logic [63:0] desc_data_ptr;
          logic [31:0] desc_data_len;
          logic [31:0] desc_data_stride;
          logic [31:0] entry_count;
          logic [31:0] entry_stride;
          desc_version = submit_words[0][15:0];
          desc_size_dw = submit_words[0][31:16];
          desc_queue_id = submit_words[1][15:0];
          desc_opcode = submit_words[1][31:16];
          desc_flags = submit_words[2];
          desc_tag = submit_words[3];
          desc_data_ptr = {submit_words[5], submit_words[4]};
          desc_data_len = submit_words[6];
          desc_data_stride = submit_words[7];
          entry_stride = (desc_data_stride == 0) ? 32'(CARBONDMA_DESC_V1_SIZE_BYTES) : desc_data_stride;
          entry_count = (desc_data_len == 0) ? 0 : (desc_data_len / entry_stride);

          queue_tag_q <= desc_tag;
          queue_opcode_q <= desc_opcode;
          queue_flags_q <= desc_flags;
          queue_data_ptr_q <= desc_data_ptr;
          queue_data_len_q <= desc_data_len;
          queue_data_stride_q <= desc_data_stride;
          queue_entry_stride_q <= entry_stride;
          queue_entry_count_q <= entry_count;
          queue_entry_index_q <= 32'h0;
          queue_bytes_done_q <= 32'h0;
          queue_status_code_q <= 16'(CARBONDMA_TURBO_STATUS_OK);
          queue_error_q <= 1'b0;

          if (desc_version != 16'd1 || desc_size_dw != 16'd8 || desc_queue_id != 16'd0) begin
            queue_status_code_q <= 16'(CARBONDMA_TURBO_STATUS_INVALID);
            comp_words[0] <= desc_tag;
            comp_words[1] <= {16'h0, 16'(CARBONDMA_TURBO_STATUS_INVALID)};
            comp_words[2] <= 32'h0;
            comp_words[3] <= 32'h0;
            mem_word_index_q <= 3'h0;
            state_q <= ST_COMP_WRITE_REQ;
          end else if (desc_opcode != 16'(CARBONDMA_OP_COPY) &&
                       desc_opcode != 16'(CARBONDMA_OP_FILL)) begin
            queue_status_code_q <= 16'(CARBONDMA_TURBO_STATUS_UNSUPPORTED);
            comp_words[0] <= desc_tag;
            comp_words[1] <= {16'h0, 16'(CARBONDMA_TURBO_STATUS_UNSUPPORTED)};
            comp_words[2] <= 32'h0;
            comp_words[3] <= 32'h0;
            mem_word_index_q <= 3'h0;
            state_q <= ST_COMP_WRITE_REQ;
          end else if (entry_count == 0) begin
            queue_status_code_q <= 16'(CARBONDMA_TURBO_STATUS_INVALID);
            comp_words[0] <= desc_tag;
            comp_words[1] <= {16'h0, 16'(CARBONDMA_TURBO_STATUS_INVALID)};
            comp_words[2] <= 32'h0;
            comp_words[3] <= 32'h0;
            mem_word_index_q <= 3'h0;
            state_q <= ST_COMP_WRITE_REQ;
          end else begin
            mem_word_index_q <= 3'h0;
            state_q <= ST_FETCH_ENTRY_REQ;
          end
        end
        ST_FETCH_ENTRY_REQ: begin
          if (mem_req_fire) begin
            state_q <= ST_FETCH_ENTRY_RESP;
          end
        end
        ST_FETCH_ENTRY_RESP: begin
          if (mem_rsp_fire) begin
            if (mem_if.rsp_code != MEM_CODE_W'(CARBON_FABRIC_RESP_OK)) begin
              queue_status_code_q <= 16'(CARBONDMA_TURBO_STATUS_FAULT);
              queue_error_q <= 1'b1;
              comp_words[0] <= queue_tag_q;
              comp_words[1] <= {16'h0, 16'(CARBONDMA_TURBO_STATUS_FAULT)};
              comp_words[2] <= queue_bytes_done_q;
              comp_words[3] <= 32'h0;
              mem_word_index_q <= 3'h0;
              state_q <= ST_COMP_WRITE_REQ;
            end else begin
              entry_words[mem_word_index_q] <= mem_if.rsp_rdata;
              if (mem_word_index_q == 3'h7) begin
                state_q <= ST_PARSE_ENTRY;
              end else begin
                mem_word_index_q <= mem_word_index_q + 1'b1;
                state_q <= ST_FETCH_ENTRY_REQ;
              end
            end
          end
        end
        ST_PARSE_ENTRY: begin
          logic [63:0] entry_src;
          logic [63:0] entry_dst;
          logic [31:0] entry_len;
          logic [31:0] entry_flags;
          logic [31:0] entry_fill;
          logic [31:0] entry_attr;
          entry_src = {entry_words[1], entry_words[0]};
          entry_dst = {entry_words[3], entry_words[2]};
          entry_len = entry_words[4];
          entry_flags = entry_words[5];
          entry_fill = entry_words[6];
          entry_attr = entry_words[7];

          if (entry_len == 0) begin
            queue_status_code_q <= 16'(CARBONDMA_TURBO_STATUS_INVALID);
            comp_words[0] <= queue_tag_q;
            comp_words[1] <= {16'h0, 16'(CARBONDMA_TURBO_STATUS_INVALID)};
            comp_words[2] <= queue_bytes_done_q;
            comp_words[3] <= 32'h0;
            mem_word_index_q <= 3'h0;
            state_q <= ST_COMP_WRITE_REQ;
          end else begin
            cmd_from_queue_q <= 1'b1;
            cmd_channel_q <= '0;
            cmd_src_q <= entry_src;
            cmd_dst_q <= entry_dst;
            cmd_len_q <= entry_len;
            cmd_remaining_q <= entry_len;
            cmd_fill_q <= (queue_opcode_q == 16'(CARBONDMA_OP_FILL)) ||
                          entry_flags[CARBONDMA_DESC_FLAG_FILL_BIT];
            cmd_fill_data_q <= entry_fill;
            cmd_attr_src_q <= entry_attr[MEM_ATTR_W-1:0];
            cmd_attr_dst_q <= entry_attr[(2*MEM_ATTR_W)-1:MEM_ATTR_W];
            cmd_error_q <= 1'b0;
            state_q <= cmd_fill_q ? ST_DMA_WRITE_REQ : ST_DMA_READ_REQ;
          end
        end
        ST_DMA_READ_REQ: begin
          if (cmd_fill_q) begin
            state_q <= ST_DMA_WRITE_REQ;
          end else if (mem_req_fire) begin
            state_q <= ST_DMA_READ_RESP;
          end
        end
        ST_DMA_READ_RESP: begin
          if (mem_rsp_fire) begin
            if (mem_if.rsp_code != MEM_CODE_W'(CARBON_FABRIC_RESP_OK)) begin
              cmd_error_q <= 1'b1;
              if (cmd_from_queue_q) begin
                queue_status_code_q <= 16'(CARBONDMA_TURBO_STATUS_FAULT);
                queue_error_q <= 1'b1;
                comp_words[0] <= queue_tag_q;
                comp_words[1] <= {16'h0, 16'(CARBONDMA_TURBO_STATUS_FAULT)};
                comp_words[2] <= queue_bytes_done_q;
                comp_words[3] <= 32'h0;
                mem_word_index_q <= 3'h0;
                state_q <= ST_COMP_WRITE_REQ;
              end else begin
                ch_busy_q[cmd_channel_q] <= 1'b0;
                ch_done_q[cmd_channel_q] <= 1'b1;
                ch_err_q[cmd_channel_q] <= 1'b1;
                state_q <= ST_IDLE;
              end
            end else begin
              read_byte_q <= mem_if.rsp_rdata[7:0];
              state_q <= ST_DMA_WRITE_REQ;
            end
          end
        end
        ST_DMA_WRITE_REQ: begin
          if (mem_req_fire) begin
            state_q <= ST_DMA_WRITE_RESP;
          end
        end
        ST_DMA_WRITE_RESP: begin
          if (mem_rsp_fire) begin
            if (mem_if.rsp_code != MEM_CODE_W'(CARBON_FABRIC_RESP_OK)) begin
              cmd_error_q <= 1'b1;
              if (cmd_from_queue_q) begin
                queue_status_code_q <= 16'(CARBONDMA_TURBO_STATUS_FAULT);
                queue_error_q <= 1'b1;
                comp_words[0] <= queue_tag_q;
                comp_words[1] <= {16'h0, 16'(CARBONDMA_TURBO_STATUS_FAULT)};
                comp_words[2] <= queue_bytes_done_q;
                comp_words[3] <= 32'h0;
                mem_word_index_q <= 3'h0;
                state_q <= ST_COMP_WRITE_REQ;
              end else begin
                ch_busy_q[cmd_channel_q] <= 1'b0;
                ch_done_q[cmd_channel_q] <= 1'b1;
                ch_err_q[cmd_channel_q] <= 1'b1;
                state_q <= ST_IDLE;
              end
            end else begin
              if (!cmd_fill_q) cmd_src_q <= cmd_src_q + 1'b1;
              cmd_dst_q <= cmd_dst_q + 1'b1;
              cmd_remaining_q <= cmd_remaining_q - 1'b1;

              if (cmd_remaining_q == 32'd1) begin
                if (cmd_from_queue_q) begin
                  queue_bytes_done_q <= queue_bytes_done_q + cmd_len_q;
                  if (queue_entry_index_q + 1 >= queue_entry_count_q) begin
                    comp_words[0] <= queue_tag_q;
                    comp_words[1] <= {16'h0, queue_status_code_q};
                    comp_words[2] <= queue_bytes_done_q + cmd_len_q;
                    comp_words[3] <= 32'h0;
                    mem_word_index_q <= 3'h0;
                    state_q <= ST_COMP_WRITE_REQ;
                  end else begin
                    queue_entry_index_q <= queue_entry_index_q + 1'b1;
                    mem_word_index_q <= 3'h0;
                    state_q <= ST_FETCH_ENTRY_REQ;
                  end
                end else begin
                  ch_busy_q[cmd_channel_q] <= 1'b0;
                  ch_done_q[cmd_channel_q] <= 1'b1;
                  ch_err_q[cmd_channel_q] <= cmd_error_q;
                  state_q <= ST_IDLE;
                end
              end else begin
                state_q <= cmd_fill_q ? ST_DMA_WRITE_REQ : ST_DMA_READ_REQ;
              end
            end
          end
        end
        ST_COMP_WRITE_REQ: begin
          if (mem_req_fire) begin
            state_q <= ST_COMP_WRITE_RESP;
          end
        end
        ST_COMP_WRITE_RESP: begin
          if (mem_rsp_fire) begin
            if (mem_word_index_q == 3'h3) begin
              queue_comp_head_q <= queue_comp_head_q + 1'b1;
              queue_submit_head_q <= queue_submit_head_q + 1'b1;
              queue_comp_doorbell_q <= 1'b1;
              mem_word_index_q <= 3'h0;
              state_q <= ST_IDLE;
            end else begin
              mem_word_index_q <= mem_word_index_q + 1'b1;
              state_q <= ST_COMP_WRITE_REQ;
            end
          end
        end
        default: begin
          state_q <= ST_IDLE;
        end
      endcase
    end
  end

endmodule : carbondma
