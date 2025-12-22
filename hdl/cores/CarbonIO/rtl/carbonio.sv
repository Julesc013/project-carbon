// Project Carbon - CarbonIO peripheral (v1.0)
// carbonio: Integrated UART/PIO/Timers/IRQ router with compat + turbo personalities.

module carbonio #(
    parameter logic [31:0] COMPAT_BASE_ADDR = 32'h0000_0000,
    parameter int unsigned UART_RX_DEPTH = carbonio_pkg::CARBONIO_UART_RX_DEPTH_DEFAULT,
    parameter int unsigned UART_TX_DEPTH = carbonio_pkg::CARBONIO_UART_TX_DEPTH_DEFAULT,
    parameter int unsigned PIO_WIDTH = carbonio_pkg::CARBONIO_PIO_WIDTH_DEFAULT,
    parameter int unsigned EDGE_FIFO_DEPTH = carbonio_pkg::CARBONIO_EDGE_FIFO_DEPTH_DEFAULT,
    parameter int unsigned TIMER_COUNT = carbonio_pkg::CARBONIO_TIMER_COUNT_DEFAULT,
    parameter int unsigned RESP_LATENCY = 1
) (
    input logic clk,
    input logic rst_n,

    fabric_if.slave compat_if,
    csr_if.slave    csr,
    dbg_if.core     dbg,
    irq_if #(.N(carbonio_pkg::CARBONIO_IRQ_SRC_COUNT)).src irq,

    input  logic       uart_rx_valid,
    input  logic [7:0] uart_rx_data,
    output logic       uart_rx_ready,
    input  logic       uart_tx_ready,
    output logic       uart_tx_valid,
    output logic [7:0] uart_tx_data,

    input  logic [PIO_WIDTH-1:0] pio_in,
    output logic [PIO_WIDTH-1:0] pio_out,
    output logic [PIO_WIDTH-1:0] pio_dir
);
  import carbon_arch_pkg::*;
  import carbonio_pkg::*;

  localparam int unsigned FAB_ADDR_W = $bits(compat_if.req_addr);
  localparam int unsigned FAB_DATA_W = $bits(compat_if.req_wdata);
  localparam int unsigned FAB_STRB_W = $bits(compat_if.req_wstrb);
  localparam int unsigned FAB_OP_W   = $bits(compat_if.req_op);
  localparam int unsigned FAB_ID_W   = $bits(compat_if.req_id);
  localparam int unsigned FAB_CODE_W = $bits(compat_if.rsp_code);
  localparam int unsigned BYTES_PER_WORD = (FAB_DATA_W / 8);

  localparam logic [15:0] CARBONIO_DEVICE_ID = 16'h0001;
  localparam logic [15:0] CARBONIO_DEVICE_VER = 16'h0001;

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
  // Feature words
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

  logic [31:0] feature_word0;
  logic [31:0] feature_word1;

  always_comb begin
    feature_word0 = 32'h0;
    feature_word1 = 32'h0;
    feature_word0 |= pack_field(UART_RX_DEPTH, CARBON_DEVFEAT_FIELD_RX_FIFO_DEPTH_LSB,
                                CARBON_DEVFEAT_FIELD_RX_FIFO_DEPTH_WIDTH);
    feature_word0 |= pack_field(UART_TX_DEPTH, CARBON_DEVFEAT_FIELD_TX_FIFO_DEPTH_LSB,
                                CARBON_DEVFEAT_FIELD_TX_FIFO_DEPTH_WIDTH);
    feature_word0 |= pack_field(TIMER_COUNT, CARBON_DEVFEAT_FIELD_TIMER_COUNT_LSB,
                                CARBON_DEVFEAT_FIELD_TIMER_COUNT_WIDTH);
    feature_word1 |= pack_field(0, CARBON_DEVFEAT_FIELD_QUEUE_COUNT_LSB,
                                CARBON_DEVFEAT_FIELD_QUEUE_COUNT_WIDTH);
  end

  // --------------------------------------------------------------------------
  // Core configuration registers
  // --------------------------------------------------------------------------
  logic cfg_enable_q;
  logic [31:0] cfg_mode_q;
  logic [31:0] uart_ctrl_q;
  logic [31:0] uart_watermark_q;
  logic [31:0] irq_enable_q;
  logic [31:0] irq_mask_q;

  logic [63:0] queue_submit_base_q;
  logic [31:0] queue_submit_mask_q;
  logic [63:0] queue_comp_base_q;
  logic [31:0] queue_comp_mask_q;

  logic [31:0] perf0_q;
  logic [31:0] perf1_q;

  // --------------------------------------------------------------------------
  // UART block
  // --------------------------------------------------------------------------
  logic uart_clear_errors;
  logic uart_rx_pop_raw;
  logic uart_tx_push_raw;
  logic [7:0] uart_tx_push_data;

  logic [7:0] uart_rx_data_out;
  logic [$clog2(UART_RX_DEPTH+1)-1:0] uart_rx_count;
  logic [$clog2(UART_TX_DEPTH+1)-1:0] uart_tx_count;
  logic uart_rx_overflow;
  logic uart_tx_overflow;
  logic [63:0] uart_rx_timestamp;

  carbonio_uart #(
      .RX_DEPTH(UART_RX_DEPTH),
      .TX_DEPTH(UART_TX_DEPTH)
  ) u_uart (
      .clk(clk),
      .rst_n(rst_n),
      .enable(cfg_enable_q && run_enable && uart_ctrl_q[CARBONIO_UART_CTRL_ENABLE_BIT]),
      .ts_enable(uart_ctrl_q[CARBONIO_UART_CTRL_TS_EN_BIT]),
      .tick_counter(tick_counter),
      .clear_errors(uart_clear_errors),
      .rx_push(uart_rx_valid),
      .rx_data(uart_rx_data),
      .rx_ready(uart_rx_ready),
      .uart_tx_ready(uart_tx_ready),
      .uart_tx_valid(uart_tx_valid),
      .uart_tx_data(uart_tx_data),
      .rx_pop(uart_rx_pop_raw),
      .rx_data_out(uart_rx_data_out),
      .tx_push(uart_tx_push_raw),
      .tx_data(uart_tx_push_data),
      .rx_count(uart_rx_count),
      .tx_count(uart_tx_count),
      .rx_overflow(uart_rx_overflow),
      .tx_overflow(uart_tx_overflow),
      .rx_timestamp(uart_rx_timestamp)
  );

  // --------------------------------------------------------------------------
  // PIO block
  // --------------------------------------------------------------------------
  logic pio_out_we;
  logic pio_dir_we;
  logic pio_filter_we;
  logic pio_match_we;
  logic [PIO_WIDTH-1:0] pio_out_wdata;
  logic [PIO_WIDTH-1:0] pio_dir_wdata;
  logic [7:0] pio_filter_len_wdata;
  logic [PIO_WIDTH-1:0] pio_match_value_wdata;
  logic [PIO_WIDTH-1:0] pio_match_mask_wdata;
  logic [7:0] pio_filter_len_q;
  logic [PIO_WIDTH-1:0] pio_match_value_q;
  logic [PIO_WIDTH-1:0] pio_match_mask_q;
  logic pio_edge_pop_raw;
  logic [PIO_WIDTH-1:0] pio_edge_data;
  logic [$clog2(EDGE_FIFO_DEPTH+1)-1:0] pio_edge_count;
  logic pio_edge_overflow;
  logic pio_match_pulse;
  logic pio_edge_pulse;

  carbonio_pio #(
      .WIDTH(PIO_WIDTH),
      .EDGE_FIFO_DEPTH(EDGE_FIFO_DEPTH)
  ) u_pio (
      .clk(clk),
      .rst_n(rst_n),
      .enable(cfg_enable_q && run_enable),
      .pio_in(pio_in),
      .pio_out(pio_out),
      .pio_dir(pio_dir),
      .out_we(pio_out_we),
      .out_wdata(pio_out_wdata),
      .dir_we(pio_dir_we),
      .dir_wdata(pio_dir_wdata),
      .filter_we(pio_filter_we),
      .filter_len_wdata(pio_filter_len_wdata),
      .match_we(pio_match_we),
      .match_value_wdata(pio_match_value_wdata),
      .match_mask_wdata(pio_match_mask_wdata),
      .edge_pop(pio_edge_pop_raw),
      .edge_data(pio_edge_data),
      .edge_count(pio_edge_count),
      .edge_overflow(pio_edge_overflow),
      .match_pulse(pio_match_pulse),
      .edge_pulse(pio_edge_pulse),
      .filter_len(pio_filter_len_q),
      .match_value(pio_match_value_q),
      .match_mask(pio_match_mask_q)
  );

  // --------------------------------------------------------------------------
  // Timer block
  // --------------------------------------------------------------------------
  logic [TIMER_COUNT-1:0] timer_load_we;
  logic [TIMER_COUNT-1:0][31:0] timer_load_wdata;
  logic [TIMER_COUNT-1:0] timer_ctrl_we;
  logic [TIMER_COUNT-1:0][31:0] timer_ctrl_wdata;
  logic [TIMER_COUNT-1:0] timer_status_clr;

  logic [63:0] tick_counter;
  logic [TIMER_COUNT-1:0][31:0] timer_load_q;
  logic [TIMER_COUNT-1:0][31:0] timer_ctrl_q;
  logic [TIMER_COUNT-1:0][31:0] timer_value_q;
  logic [TIMER_COUNT-1:0] timer_expired_q;
  logic [TIMER_COUNT-1:0] timer_expired_pulse;

  carbonio_timer #(
      .NUM_TIMERS(TIMER_COUNT)
  ) u_timer (
      .clk(clk),
      .rst_n(rst_n),
      .enable(cfg_enable_q && run_enable),
      .load_we(timer_load_we),
      .load_wdata(timer_load_wdata),
      .ctrl_we(timer_ctrl_we),
      .ctrl_wdata(timer_ctrl_wdata),
      .status_clr(timer_status_clr),
      .tick_counter(tick_counter),
      .load_q(timer_load_q),
      .ctrl_q(timer_ctrl_q),
      .value_q(timer_value_q),
      .expired_q(timer_expired_q),
      .expired_pulse(timer_expired_pulse)
  );

  // --------------------------------------------------------------------------
  // IRQ router
  // --------------------------------------------------------------------------
  logic [CARBONIO_IRQ_SRC_COUNT-1:0] irq_src_pulse;
  logic [CARBONIO_IRQ_SRC_COUNT-1:0] irq_pending;
  logic [CARBONIO_IRQ_SRC_COUNT-1:0] irq_clear;

  carbonio_irq_router #(
      .N_SOURCES(CARBONIO_IRQ_SRC_COUNT)
  ) u_irq (
      .clk(clk),
      .rst_n(rst_n),
      .src_pulse(irq_src_pulse),
      .enable(irq_enable_q[CARBONIO_IRQ_SRC_COUNT-1:0] & ~irq_mask_q[CARBONIO_IRQ_SRC_COUNT-1:0]),
      .clear(irq_clear),
      .pending(irq_pending),
      .irq_out(irq)
  );

  // UART watermarks (rx >= rx_wm, tx <= tx_wm).
  wire [7:0] uart_rx_wm = uart_watermark_q[7:0];
  wire [7:0] uart_tx_wm = uart_watermark_q[15:8];
  logic uart_rx_wm_hit_q;
  logic uart_tx_wm_hit_q;

  wire uart_rx_wm_hit = (uart_rx_count >= uart_rx_wm) && (uart_rx_wm != 0);
  wire uart_tx_wm_hit = (uart_tx_count <= uart_tx_wm);

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      uart_rx_wm_hit_q <= 1'b0;
      uart_tx_wm_hit_q <= 1'b0;
    end else begin
      uart_rx_wm_hit_q <= uart_rx_wm_hit;
      uart_tx_wm_hit_q <= uart_tx_wm_hit;
    end
  end

  assign irq_src_pulse[CARBONIO_IRQ_SRC_UART_RX] = uart_rx_wm_hit && !uart_rx_wm_hit_q;
  assign irq_src_pulse[CARBONIO_IRQ_SRC_UART_TX] = uart_tx_wm_hit && !uart_tx_wm_hit_q;
  assign irq_src_pulse[CARBONIO_IRQ_SRC_PIO_EDGE] = pio_edge_pulse;
  assign irq_src_pulse[CARBONIO_IRQ_SRC_PIO_MATCH] = pio_match_pulse;
  assign irq_src_pulse[CARBONIO_IRQ_SRC_TIMER0] = timer_expired_pulse[0];
  assign irq_src_pulse[CARBONIO_IRQ_SRC_TIMER1] = (TIMER_COUNT > 1) ? timer_expired_pulse[1] : 1'b0;

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

  // CSR pulses/side-effects.
  logic csr_uart_rx_pop;
  logic csr_uart_tx_push;
  logic [7:0] csr_uart_tx_data;
  logic csr_pio_edge_pop;
  logic csr_timer0_status_clr;
  logic csr_timer1_status_clr;
  logic [CARBONIO_IRQ_SRC_COUNT-1:0] csr_irq_clear_pulse;
  logic csr_uart_clear_errors;
  logic compat_uart_clear_errors;

  logic csr_pio_out_we;
  logic csr_pio_dir_we;
  logic csr_pio_filter_we;
  logic csr_pio_match_we;
  logic [PIO_WIDTH-1:0] csr_pio_out_wdata;
  logic [PIO_WIDTH-1:0] csr_pio_dir_wdata;
  logic [7:0] csr_pio_filter_len;
  logic [PIO_WIDTH-1:0] csr_pio_match_value;
  logic [PIO_WIDTH-1:0] csr_pio_match_mask;

  logic [TIMER_COUNT-1:0] csr_timer_load_we;
  logic [TIMER_COUNT-1:0][31:0] csr_timer_load_wdata;
  logic [TIMER_COUNT-1:0] csr_timer_ctrl_we;
  logic [TIMER_COUNT-1:0][31:0] csr_timer_ctrl_wdata;
  logic [TIMER_COUNT-1:0] csr_timer_status_clr_vec;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      cfg_enable_q <= 1'b1;
      cfg_mode_q <= 32'h0;
      uart_ctrl_q <= 32'(1 << CARBONIO_UART_CTRL_ENABLE_BIT);
      uart_watermark_q <= {8'd1, 8'd1, 16'h0};
      irq_enable_q <= '0;
      irq_mask_q <= '0;

      queue_submit_base_q <= 64'h0;
      queue_submit_mask_q <= 32'h0;
      queue_comp_base_q <= 64'h0;
      queue_comp_mask_q <= 32'h0;

      perf0_q <= 32'h0;
      perf1_q <= 32'h0;

      csr_rsp_valid_q <= 1'b0;
      csr_rsp_rdata_q <= 32'h0;
      csr_rsp_fault_q <= 1'b0;
      csr_rsp_side_q <= 1'b0;

      csr_uart_rx_pop <= 1'b0;
      csr_uart_tx_push <= 1'b0;
      csr_uart_tx_data <= 8'h0;
      csr_pio_edge_pop <= 1'b0;
      csr_timer0_status_clr <= 1'b0;
      csr_timer1_status_clr <= 1'b0;
      csr_irq_clear_pulse <= '0;
      csr_uart_clear_errors <= 1'b0;

      csr_pio_out_we <= 1'b0;
      csr_pio_dir_we <= 1'b0;
      csr_pio_filter_we <= 1'b0;
      csr_pio_match_we <= 1'b0;
      csr_pio_out_wdata <= '0;
      csr_pio_dir_wdata <= '0;
      csr_pio_filter_len <= 8'h0;
      csr_pio_match_value <= '0;
      csr_pio_match_mask <= '0;

      csr_timer_load_we <= '0;
      csr_timer_load_wdata <= '0;
      csr_timer_ctrl_we <= '0;
      csr_timer_ctrl_wdata <= '0;
    end else begin
      csr_uart_rx_pop <= 1'b0;
      csr_uart_tx_push <= 1'b0;
      csr_pio_edge_pop <= 1'b0;
      csr_timer0_status_clr <= 1'b0;
      csr_timer1_status_clr <= 1'b0;
      csr_irq_clear_pulse <= '0;
      csr_uart_clear_errors <= 1'b0;
      csr_rsp_side_q <= 1'b0;
      csr_rsp_fault_q <= 1'b0;

      csr_pio_out_we <= 1'b0;
      csr_pio_dir_we <= 1'b0;
      csr_pio_filter_we <= 1'b0;
      csr_pio_match_we <= 1'b0;
      csr_timer_load_we <= '0;
      csr_timer_ctrl_we <= '0;

      if (csr_rsp_fire) begin
        csr_rsp_valid_q <= 1'b0;
      end

      if (compat_req_fire && compat_if.req_op == FAB_OP_W'(CARBON_FABRIC_XACT_WRITE)) begin
        logic [31:0] compat_addr_off;
        compat_addr_off = compat_if.req_addr - COMPAT_BASE_ADDR;
        unique case (compat_addr_off & 32'hFFFF_FFFC)
          CARBONIO_COMPAT_UART_CTRL_OFF: begin
            uart_ctrl_q <= apply_wstrb(uart_ctrl_q, compat_if.req_wdata, compat_if.req_wstrb) &
                           ~(32'(1) << CARBONIO_UART_CTRL_CLR_ERR_BIT);
          end
          CARBONIO_COMPAT_UART_WATERMARKS_OFF: begin
            uart_watermark_q <= apply_wstrb(uart_watermark_q, compat_if.req_wdata, compat_if.req_wstrb);
          end
          CARBONIO_COMPAT_IRQ_ENABLE_OFF: begin
            irq_enable_q <= apply_wstrb(irq_enable_q, compat_if.req_wdata, compat_if.req_wstrb);
          end
          CARBONIO_COMPAT_IRQ_MASK_OFF: begin
            irq_mask_q <= apply_wstrb(irq_mask_q, compat_if.req_wdata, compat_if.req_wstrb);
          end
          default: begin
          end
        endcase
      end

      if (csr_req_fire) begin
        csr_rsp_valid_q <= 1'b1;
        csr_rsp_rdata_q <= 32'h0;
        csr_rsp_fault_q <= 1'b0;
        csr_rsp_side_q <= csr.req_write;

        unique case (csr.req_addr)
          CARBON_CSR_CARBONIO_ID: begin
            if (!csr.req_write) csr_rsp_rdata_q <= {CARBONIO_DEVICE_VER, CARBONIO_DEVICE_ID};
            else csr_rsp_fault_q <= 1'b1;
          end
          CARBON_CSR_CARBONIO_STATUS: begin
            csr_rsp_rdata_q[0] <= cfg_enable_q;
            csr_rsp_rdata_q[1] <= uart_rx_overflow;
            csr_rsp_rdata_q[2] <= uart_tx_overflow;
            csr_rsp_rdata_q[3] <= pio_edge_overflow;
            csr_rsp_rdata_q[4] <= timer_expired_q[0];
            csr_rsp_rdata_q[5] <= (TIMER_COUNT > 1) ? timer_expired_q[1] : 1'b0;
          end
          CARBON_CSR_CARBONIO_CTRL: begin
            if (csr.req_write) begin
              cfg_enable_q <= csr.req_wdata[0];
              if (csr.req_wdata[1]) csr_uart_clear_errors <= 1'b1;
              csr_rsp_side_q <= 1'b1;
            end else begin
              csr_rsp_rdata_q[0] <= cfg_enable_q;
            end
          end
          CARBON_CSR_CARBONIO_MODE: begin
            if (csr.req_write) begin
              cfg_mode_q <= csr.req_wdata;
              csr_rsp_side_q <= 1'b1;
            end else begin
              csr_rsp_rdata_q <= cfg_mode_q;
            end
          end
          CARBON_CSR_CARBONIO_FEATURE0: begin
            if (!csr.req_write) csr_rsp_rdata_q <= feature_word0;
            else csr_rsp_fault_q <= 1'b1;
          end
          CARBON_CSR_CARBONIO_FEATURE1: begin
            if (!csr.req_write) csr_rsp_rdata_q <= feature_word1;
            else csr_rsp_fault_q <= 1'b1;
          end

          CARBON_CSR_CARBONIO_QUEUE_SUBMIT_BASE_LO: begin
            if (csr.req_write) queue_submit_base_q[31:0] <= csr.req_wdata;
            else csr_rsp_rdata_q <= queue_submit_base_q[31:0];
          end
          CARBON_CSR_CARBONIO_QUEUE_SUBMIT_BASE_HI: begin
            if (csr.req_write) queue_submit_base_q[63:32] <= csr.req_wdata;
            else csr_rsp_rdata_q <= queue_submit_base_q[63:32];
          end
          CARBON_CSR_CARBONIO_QUEUE_SUBMIT_MASK: begin
            if (csr.req_write) queue_submit_mask_q <= csr.req_wdata;
            else csr_rsp_rdata_q <= queue_submit_mask_q;
          end
          CARBON_CSR_CARBONIO_QUEUE_DOORBELL: begin
            if (!csr.req_write) csr_rsp_fault_q <= 1'b1;
            // TODO: wire turbo UART queue in v2.
          end
          CARBON_CSR_CARBONIO_QUEUE_COMP_BASE_LO: begin
            if (csr.req_write) queue_comp_base_q[31:0] <= csr.req_wdata;
            else csr_rsp_rdata_q <= queue_comp_base_q[31:0];
          end
          CARBON_CSR_CARBONIO_QUEUE_COMP_BASE_HI: begin
            if (csr.req_write) queue_comp_base_q[63:32] <= csr.req_wdata;
            else csr_rsp_rdata_q <= queue_comp_base_q[63:32];
          end
          CARBON_CSR_CARBONIO_QUEUE_COMP_MASK: begin
            if (csr.req_write) queue_comp_mask_q <= csr.req_wdata;
            else csr_rsp_rdata_q <= queue_comp_mask_q;
          end
          CARBON_CSR_CARBONIO_QUEUE_COMP_DOORBELL: begin
            csr_rsp_rdata_q <= 32'h0;
          end
          CARBON_CSR_CARBONIO_QUEUE_STATUS: begin
            csr_rsp_rdata_q <= 32'h0;
          end
          CARBON_CSR_CARBONIO_PERF0: begin
            csr_rsp_rdata_q <= perf0_q;
          end
          CARBON_CSR_CARBONIO_PERF1: begin
            csr_rsp_rdata_q <= perf1_q;
          end

          CARBON_CSR_CARBONIO_UART_CFG: begin
            if (csr.req_write) begin
              uart_ctrl_q <= csr.req_wdata & ~(32'(1) << CARBONIO_UART_CTRL_CLR_ERR_BIT);
              if (csr.req_wdata[CARBONIO_UART_CTRL_CLR_ERR_BIT]) csr_uart_clear_errors <= 1'b1;
              csr_rsp_side_q <= 1'b1;
            end else begin
              csr_rsp_rdata_q <= uart_ctrl_q;
            end
          end
          CARBON_CSR_CARBONIO_UART_STATUS: begin
            csr_rsp_rdata_q[CARBONIO_UART_STATUS_RX_AVAIL_BIT] <= (uart_rx_count != 0);
            csr_rsp_rdata_q[CARBONIO_UART_STATUS_TX_SPACE_BIT] <= (uart_tx_count < UART_TX_DEPTH);
            csr_rsp_rdata_q[CARBONIO_UART_STATUS_RX_OVF_BIT] <= uart_rx_overflow;
            csr_rsp_rdata_q[CARBONIO_UART_STATUS_TX_OVF_BIT] <= uart_tx_overflow;
          end
          CARBON_CSR_CARBONIO_UART_RX_COUNT: begin
            csr_rsp_rdata_q <= uart_rx_count;
          end
          CARBON_CSR_CARBONIO_UART_TX_COUNT: begin
            csr_rsp_rdata_q <= uart_tx_count;
          end
          CARBON_CSR_CARBONIO_UART_TX_WDATA: begin
            if (csr.req_write) begin
              csr_uart_tx_push <= 1'b1;
              csr_uart_tx_data <= csr.req_wdata[7:0];
              csr_rsp_side_q <= 1'b1;
            end else begin
              csr_rsp_fault_q <= 1'b1;
            end
          end
          CARBON_CSR_CARBONIO_UART_RX_RDATA: begin
            if (!csr.req_write) begin
              csr_rsp_rdata_q[7:0] <= uart_rx_data_out;
              csr_uart_rx_pop <= 1'b1;
            end else begin
              csr_rsp_fault_q <= 1'b1;
            end
          end
          CARBON_CSR_CARBONIO_UART_WATERMARKS: begin
            if (csr.req_write) begin
              uart_watermark_q <= csr.req_wdata;
              csr_rsp_side_q <= 1'b1;
            end else begin
              csr_rsp_rdata_q <= uart_watermark_q;
            end
          end
          CARBON_CSR_CARBONIO_UART_TS_LO: begin
            csr_rsp_rdata_q <= uart_rx_timestamp[31:0];
          end
          CARBON_CSR_CARBONIO_UART_TS_HI: begin
            csr_rsp_rdata_q <= uart_rx_timestamp[63:32];
          end

          CARBON_CSR_CARBONIO_PIO_IN: begin
            csr_rsp_rdata_q <= pio_in;
          end
          CARBON_CSR_CARBONIO_PIO_OUT: begin
            if (csr.req_write) begin
              csr_pio_out_we <= 1'b1;
              csr_pio_out_wdata <= csr.req_wdata;
              csr_rsp_side_q <= 1'b1;
            end else begin
              csr_rsp_rdata_q <= pio_out;
            end
          end
          CARBON_CSR_CARBONIO_PIO_DIR: begin
            if (csr.req_write) begin
              csr_pio_dir_we <= 1'b1;
              csr_pio_dir_wdata <= csr.req_wdata;
              csr_rsp_side_q <= 1'b1;
            end else begin
              csr_rsp_rdata_q <= pio_dir;
            end
          end
          CARBON_CSR_CARBONIO_PIO_EDGE_RDATA: begin
            csr_rsp_rdata_q <= pio_edge_data;
            csr_pio_edge_pop <= 1'b1;
          end
          CARBON_CSR_CARBONIO_PIO_EDGE_COUNT: begin
            csr_rsp_rdata_q <= pio_edge_count;
          end
          CARBON_CSR_CARBONIO_PIO_FILTER_CFG: begin
            if (csr.req_write) begin
              csr_pio_filter_we <= 1'b1;
              csr_pio_filter_len <= csr.req_wdata[7:0];
              csr_rsp_side_q <= 1'b1;
            end else begin
              csr_rsp_rdata_q[7:0] <= pio_filter_len_q;
            end
          end
          CARBON_CSR_CARBONIO_PIO_MATCH_CFG: begin
            if (csr.req_write) begin
              csr_pio_match_we <= 1'b1;
              csr_pio_match_value <= csr.req_wdata;
              csr_pio_match_mask <= 32'hFFFF_FFFF;
              csr_rsp_side_q <= 1'b1;
            end else begin
              csr_rsp_rdata_q <= pio_match_value_q;
            end
          end

          CARBON_CSR_CARBONIO_TICK_LO: begin
            csr_rsp_rdata_q <= tick_counter[31:0];
          end
          CARBON_CSR_CARBONIO_TICK_HI: begin
            csr_rsp_rdata_q <= tick_counter[63:32];
          end
          CARBON_CSR_CARBONIO_TIMER0_LOAD: begin
            if (csr.req_write) begin
              csr_timer_load_we[0] <= 1'b1;
              csr_timer_load_wdata[0] <= csr.req_wdata;
              csr_rsp_side_q <= 1'b1;
            end else begin
              csr_rsp_rdata_q <= timer_load_q[0];
            end
          end
          CARBON_CSR_CARBONIO_TIMER0_VALUE: begin
            csr_rsp_rdata_q <= timer_value_q[0];
          end
          CARBON_CSR_CARBONIO_TIMER0_CTRL: begin
            if (csr.req_write) begin
              csr_timer_ctrl_we[0] <= 1'b1;
              csr_timer_ctrl_wdata[0] <= csr.req_wdata;
              csr_rsp_side_q <= 1'b1;
            end else begin
              csr_rsp_rdata_q <= timer_ctrl_q[0];
            end
          end
          CARBON_CSR_CARBONIO_TIMER0_STATUS: begin
            csr_rsp_rdata_q[0] <= timer_expired_q[0];
            if (csr.req_write) csr_timer0_status_clr <= 1'b1;
          end
          CARBON_CSR_CARBONIO_TIMER1_LOAD: begin
            if (TIMER_COUNT > 1) begin
              if (csr.req_write) begin
                csr_timer_load_we[1] <= 1'b1;
                csr_timer_load_wdata[1] <= csr.req_wdata;
                csr_rsp_side_q <= 1'b1;
              end else begin
                csr_rsp_rdata_q <= timer_load_q[1];
              end
            end else csr_rsp_fault_q <= 1'b1;
          end
          CARBON_CSR_CARBONIO_TIMER1_VALUE: begin
            if (TIMER_COUNT > 1) csr_rsp_rdata_q <= timer_value_q[1];
            else csr_rsp_fault_q <= 1'b1;
          end
          CARBON_CSR_CARBONIO_TIMER1_CTRL: begin
            if (TIMER_COUNT > 1) begin
              if (csr.req_write) begin
                csr_timer_ctrl_we[1] <= 1'b1;
                csr_timer_ctrl_wdata[1] <= csr.req_wdata;
                csr_rsp_side_q <= 1'b1;
              end else begin
                csr_rsp_rdata_q <= timer_ctrl_q[1];
              end
            end else csr_rsp_fault_q <= 1'b1;
          end
          CARBON_CSR_CARBONIO_TIMER1_STATUS: begin
            if (TIMER_COUNT > 1) begin
              csr_rsp_rdata_q[0] <= timer_expired_q[1];
              if (csr.req_write) csr_timer1_status_clr <= 1'b1;
            end else csr_rsp_fault_q <= 1'b1;
          end

          CARBON_CSR_CARBONIO_IRQ_ENABLE: begin
            if (csr.req_write) begin
              irq_enable_q <= csr.req_wdata;
              csr_rsp_side_q <= 1'b1;
            end else begin
              csr_rsp_rdata_q <= irq_enable_q;
            end
          end
          CARBON_CSR_CARBONIO_IRQ_PENDING: begin
            csr_rsp_rdata_q[CARBONIO_IRQ_SRC_COUNT-1:0] <= irq_pending;
          end
          CARBON_CSR_CARBONIO_IRQ_MASK: begin
            if (csr.req_write) begin
              irq_mask_q <= csr.req_wdata;
              csr_irq_clear_pulse <= csr.req_wdata[CARBONIO_IRQ_SRC_COUNT-1:0];
              csr_rsp_side_q <= 1'b1;
            end else begin
              csr_rsp_rdata_q <= irq_mask_q;
            end
          end

          default: begin
            csr_rsp_fault_q <= 1'b1;
          end
        endcase
      end

      if (uart_tx_valid) perf0_q <= perf0_q + 1'b1;
      if (uart_rx_valid && uart_rx_ready) perf1_q <= perf1_q + 1'b1;
    end
  end

  // --------------------------------------------------------------------------
  // Compatibility (fabric) interface
  // --------------------------------------------------------------------------
  logic compat_rsp_valid_q;
  logic [FAB_DATA_W-1:0] compat_rsp_rdata_q;
  logic [FAB_CODE_W-1:0] compat_rsp_code_q;
  logic [FAB_ID_W-1:0] compat_rsp_id_q;
  logic compat_busy_q;
  logic [31:0] compat_delay_q;

  assign compat_if.req_ready = !compat_busy_q;
  assign compat_if.rsp_valid = compat_rsp_valid_q;
  assign compat_if.rsp_rdata = compat_rsp_rdata_q;
  assign compat_if.rsp_code  = compat_rsp_code_q;
  assign compat_if.rsp_id    = compat_rsp_id_q;

  wire compat_req_fire = compat_if.req_valid && compat_if.req_ready;
  wire compat_rsp_fire = compat_if.rsp_valid && compat_if.rsp_ready;

  // Compat pulses
  logic compat_uart_rx_pop;
  logic compat_uart_tx_push;
  logic [7:0] compat_uart_tx_data;
  logic compat_pio_edge_pop;
  logic compat_timer0_status_clr;
  logic compat_timer1_status_clr;
  logic [CARBONIO_IRQ_SRC_COUNT-1:0] compat_irq_clear_pulse;

  logic compat_pio_out_we;
  logic compat_pio_dir_we;
  logic compat_pio_filter_we;
  logic compat_pio_match_we;
  logic [PIO_WIDTH-1:0] compat_pio_out_wdata;
  logic [PIO_WIDTH-1:0] compat_pio_dir_wdata;
  logic [7:0] compat_pio_filter_len;
  logic [PIO_WIDTH-1:0] compat_pio_match_value;
  logic [PIO_WIDTH-1:0] compat_pio_match_mask;

  logic [TIMER_COUNT-1:0] compat_timer_load_we;
  logic [TIMER_COUNT-1:0][31:0] compat_timer_load_wdata;
  logic [TIMER_COUNT-1:0] compat_timer_ctrl_we;
  logic [TIMER_COUNT-1:0][31:0] compat_timer_ctrl_wdata;
  logic [TIMER_COUNT-1:0] compat_timer_status_clr_vec;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      compat_rsp_valid_q <= 1'b0;
      compat_rsp_rdata_q <= '0;
      compat_rsp_code_q <= '0;
      compat_rsp_id_q <= '0;
      compat_busy_q <= 1'b0;
      compat_delay_q <= '0;

      compat_uart_rx_pop <= 1'b0;
      compat_uart_tx_push <= 1'b0;
      compat_uart_tx_data <= 8'h0;
      compat_pio_edge_pop <= 1'b0;
      compat_timer0_status_clr <= 1'b0;
      compat_timer1_status_clr <= 1'b0;
      compat_uart_clear_errors <= 1'b0;
      compat_irq_clear_pulse <= '0;

      compat_pio_out_we <= 1'b0;
      compat_pio_dir_we <= 1'b0;
      compat_pio_filter_we <= 1'b0;
      compat_pio_match_we <= 1'b0;
      compat_pio_out_wdata <= '0;
      compat_pio_dir_wdata <= '0;
      compat_pio_filter_len <= 8'h0;
      compat_pio_match_value <= '0;
      compat_pio_match_mask <= '0;

      compat_timer_load_we <= '0;
      compat_timer_load_wdata <= '0;
      compat_timer_ctrl_we <= '0;
      compat_timer_ctrl_wdata <= '0;
    end else begin
      compat_uart_rx_pop <= 1'b0;
      compat_uart_tx_push <= 1'b0;
      compat_pio_edge_pop <= 1'b0;
      compat_timer0_status_clr <= 1'b0;
      compat_timer1_status_clr <= 1'b0;
      compat_uart_clear_errors <= 1'b0;
      compat_irq_clear_pulse <= '0;
      compat_pio_out_we <= 1'b0;
      compat_pio_dir_we <= 1'b0;
      compat_pio_filter_we <= 1'b0;
      compat_pio_match_we <= 1'b0;
      compat_timer_load_we <= '0;
      compat_timer_ctrl_we <= '0;

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

      if (compat_req_fire) begin
        compat_busy_q <= 1'b1;
        compat_delay_q <= RESP_LATENCY;
        compat_rsp_id_q <= compat_if.req_id;
        compat_rsp_rdata_q <= '0;
        compat_rsp_code_q <= FAB_CODE_W'(CARBON_FABRIC_RESP_OK);

        if (compat_if.req_op == FAB_OP_W'(CARBON_FABRIC_XACT_READ)) begin
          logic [31:0] addr_off;
          addr_off = compat_if.req_addr - COMPAT_BASE_ADDR;
          unique case (addr_off & 32'hFFFF_FFFC)
            CARBONIO_COMPAT_UART_DATA_OFF: begin
              compat_rsp_rdata_q[7:0] <= uart_rx_data_out;
              compat_uart_rx_pop <= 1'b1;
            end
            CARBONIO_COMPAT_UART_STATUS_OFF: begin
              compat_rsp_rdata_q[CARBONIO_UART_STATUS_RX_AVAIL_BIT] <= (uart_rx_count != 0);
              compat_rsp_rdata_q[CARBONIO_UART_STATUS_TX_SPACE_BIT] <= (uart_tx_count < UART_TX_DEPTH);
              compat_rsp_rdata_q[CARBONIO_UART_STATUS_RX_OVF_BIT] <= uart_rx_overflow;
              compat_rsp_rdata_q[CARBONIO_UART_STATUS_TX_OVF_BIT] <= uart_tx_overflow;
            end
            CARBONIO_COMPAT_UART_CTRL_OFF: begin
              compat_rsp_rdata_q <= uart_ctrl_q;
            end
            CARBONIO_COMPAT_UART_RX_COUNT_OFF: begin
              compat_rsp_rdata_q <= uart_rx_count;
            end
            CARBONIO_COMPAT_UART_TX_COUNT_OFF: begin
              compat_rsp_rdata_q <= uart_tx_count;
            end
            CARBONIO_COMPAT_UART_TS_LO_OFF: begin
              compat_rsp_rdata_q <= uart_rx_timestamp[31:0];
            end
            CARBONIO_COMPAT_UART_TS_HI_OFF: begin
              compat_rsp_rdata_q <= uart_rx_timestamp[63:32];
            end
            CARBONIO_COMPAT_UART_WATERMARKS_OFF: begin
              compat_rsp_rdata_q <= uart_watermark_q;
            end
            CARBONIO_COMPAT_PIO_IN_OFF: begin
              compat_rsp_rdata_q <= pio_in;
            end
            CARBONIO_COMPAT_PIO_OUT_OFF: begin
              compat_rsp_rdata_q <= pio_out;
            end
            CARBONIO_COMPAT_PIO_DIR_OFF: begin
              compat_rsp_rdata_q <= pio_dir;
            end
            CARBONIO_COMPAT_PIO_EDGE_RDATA_OFF: begin
              compat_rsp_rdata_q <= pio_edge_data;
              compat_pio_edge_pop <= 1'b1;
            end
            CARBONIO_COMPAT_PIO_EDGE_COUNT_OFF: begin
              compat_rsp_rdata_q <= pio_edge_count;
            end
            CARBONIO_COMPAT_PIO_FILTER_CFG_OFF: begin
              compat_rsp_rdata_q[7:0] <= pio_filter_len_q;
            end
            CARBONIO_COMPAT_PIO_MATCH_CFG_OFF: begin
              compat_rsp_rdata_q <= pio_match_value_q;
            end
            CARBONIO_COMPAT_TICK_LO_OFF: begin
              compat_rsp_rdata_q <= tick_counter[31:0];
            end
            CARBONIO_COMPAT_TICK_HI_OFF: begin
              compat_rsp_rdata_q <= tick_counter[63:32];
            end
            CARBONIO_COMPAT_TIMER0_LOAD_OFF: begin
              compat_rsp_rdata_q <= timer_load_q[0];
            end
            CARBONIO_COMPAT_TIMER0_VALUE_OFF: begin
              compat_rsp_rdata_q <= timer_value_q[0];
            end
            CARBONIO_COMPAT_TIMER0_CTRL_OFF: begin
              compat_rsp_rdata_q <= timer_ctrl_q[0];
            end
            CARBONIO_COMPAT_TIMER0_STATUS_OFF: begin
              compat_rsp_rdata_q[0] <= timer_expired_q[0];
            end
            CARBONIO_COMPAT_TIMER1_LOAD_OFF: begin
              compat_rsp_rdata_q <= (TIMER_COUNT > 1) ? timer_load_q[1] : 32'h0;
            end
            CARBONIO_COMPAT_TIMER1_VALUE_OFF: begin
              compat_rsp_rdata_q <= (TIMER_COUNT > 1) ? timer_value_q[1] : 32'h0;
            end
            CARBONIO_COMPAT_TIMER1_CTRL_OFF: begin
              compat_rsp_rdata_q <= (TIMER_COUNT > 1) ? timer_ctrl_q[1] : 32'h0;
            end
            CARBONIO_COMPAT_TIMER1_STATUS_OFF: begin
              compat_rsp_rdata_q[0] <= (TIMER_COUNT > 1) ? timer_expired_q[1] : 1'b0;
            end
            CARBONIO_COMPAT_IRQ_ENABLE_OFF: begin
              compat_rsp_rdata_q <= irq_enable_q;
            end
            CARBONIO_COMPAT_IRQ_PENDING_OFF: begin
              compat_rsp_rdata_q[CARBONIO_IRQ_SRC_COUNT-1:0] <= irq_pending;
            end
            CARBONIO_COMPAT_IRQ_MASK_OFF: begin
              compat_rsp_rdata_q <= irq_mask_q;
            end
            default: begin
              compat_rsp_code_q <= FAB_CODE_W'(CARBON_FABRIC_RESP_ACCESS_FAULT);
            end
          endcase
        end else if (compat_if.req_op == FAB_OP_W'(CARBON_FABRIC_XACT_WRITE)) begin
          logic [31:0] addr_off;
          addr_off = compat_if.req_addr - COMPAT_BASE_ADDR;
          unique case (addr_off & 32'hFFFF_FFFC)
            CARBONIO_COMPAT_UART_DATA_OFF: begin
              if (compat_if.req_wstrb[0]) begin
                compat_uart_tx_push <= 1'b1;
                compat_uart_tx_data <= compat_if.req_wdata[7:0];
              end
            end
            CARBONIO_COMPAT_UART_CTRL_OFF: begin
              if (compat_if.req_wdata[CARBONIO_UART_CTRL_CLR_ERR_BIT]) compat_uart_clear_errors <= 1'b1;
            end
            CARBONIO_COMPAT_UART_WATERMARKS_OFF: begin
            end
            CARBONIO_COMPAT_PIO_OUT_OFF: begin
              compat_pio_out_we <= 1'b1;
              compat_pio_out_wdata <= apply_wstrb(pio_out, compat_if.req_wdata, compat_if.req_wstrb);
            end
            CARBONIO_COMPAT_PIO_DIR_OFF: begin
              compat_pio_dir_we <= 1'b1;
              compat_pio_dir_wdata <= apply_wstrb(pio_dir, compat_if.req_wdata, compat_if.req_wstrb);
            end
            CARBONIO_COMPAT_PIO_FILTER_CFG_OFF: begin
              compat_pio_filter_we <= 1'b1;
              compat_pio_filter_len <= compat_if.req_wdata[7:0];
            end
            CARBONIO_COMPAT_PIO_MATCH_CFG_OFF: begin
              compat_pio_match_we <= 1'b1;
              compat_pio_match_value <= compat_if.req_wdata;
              compat_pio_match_mask <= 32'hFFFF_FFFF;
            end
            CARBONIO_COMPAT_TIMER0_LOAD_OFF: begin
              compat_timer_load_we[0] <= 1'b1;
              compat_timer_load_wdata[0] <= compat_if.req_wdata;
            end
            CARBONIO_COMPAT_TIMER0_CTRL_OFF: begin
              compat_timer_ctrl_we[0] <= 1'b1;
              compat_timer_ctrl_wdata[0] <= compat_if.req_wdata;
            end
            CARBONIO_COMPAT_TIMER0_STATUS_OFF: begin
              compat_timer0_status_clr <= 1'b1;
            end
            CARBONIO_COMPAT_TIMER1_LOAD_OFF: begin
              if (TIMER_COUNT > 1) begin
                compat_timer_load_we[1] <= 1'b1;
                compat_timer_load_wdata[1] <= compat_if.req_wdata;
              end
            end
            CARBONIO_COMPAT_TIMER1_CTRL_OFF: begin
              if (TIMER_COUNT > 1) begin
                compat_timer_ctrl_we[1] <= 1'b1;
                compat_timer_ctrl_wdata[1] <= compat_if.req_wdata;
              end
            end
            CARBONIO_COMPAT_TIMER1_STATUS_OFF: begin
              if (TIMER_COUNT > 1) begin
                compat_timer1_status_clr <= 1'b1;
              end
            end
            CARBONIO_COMPAT_IRQ_ENABLE_OFF: begin
            end
            CARBONIO_COMPAT_IRQ_MASK_OFF: begin
              compat_irq_clear_pulse <= compat_if.req_wdata[CARBONIO_IRQ_SRC_COUNT-1:0];
            end
            default: begin
              compat_rsp_code_q <= FAB_CODE_W'(CARBON_FABRIC_RESP_ACCESS_FAULT);
            end
          endcase
        end else begin
          compat_rsp_code_q <= FAB_CODE_W'(CARBON_FABRIC_RESP_ACCESS_FAULT);
        end
      end
    end
  end

  // --------------------------------------------------------------------------
  // Combined side effects (CSR + compat)
  // --------------------------------------------------------------------------
  assign uart_clear_errors = csr_uart_clear_errors | compat_uart_clear_errors;
  assign uart_rx_pop_raw = csr_uart_rx_pop | (compat_uart_rx_pop && !csr_uart_rx_pop);
  assign uart_tx_push_raw = csr_uart_tx_push | (compat_uart_tx_push && !csr_uart_tx_push);
  assign uart_tx_push_data = csr_uart_tx_push ? csr_uart_tx_data : compat_uart_tx_data;

  assign pio_edge_pop_raw = csr_pio_edge_pop | (compat_pio_edge_pop && !csr_pio_edge_pop);

  assign pio_out_we = csr_pio_out_we | compat_pio_out_we;
  assign pio_dir_we = csr_pio_dir_we | compat_pio_dir_we;
  assign pio_filter_we = csr_pio_filter_we | compat_pio_filter_we;
  assign pio_match_we = csr_pio_match_we | compat_pio_match_we;

  assign pio_out_wdata = csr_pio_out_we ? csr_pio_out_wdata : compat_pio_out_wdata;
  assign pio_dir_wdata = csr_pio_dir_we ? csr_pio_dir_wdata : compat_pio_dir_wdata;
  assign pio_filter_len_wdata = csr_pio_filter_we ? csr_pio_filter_len : compat_pio_filter_len;
  assign pio_match_value_wdata = csr_pio_match_we ? csr_pio_match_value : compat_pio_match_value;
  assign pio_match_mask_wdata = csr_pio_match_we ? csr_pio_match_mask : compat_pio_match_mask;

  always_comb begin
    csr_timer_status_clr_vec = '0;
    compat_timer_status_clr_vec = '0;
    csr_timer_status_clr_vec[0] = csr_timer0_status_clr;
    compat_timer_status_clr_vec[0] = compat_timer0_status_clr;
    if (TIMER_COUNT > 1) begin
      csr_timer_status_clr_vec[1] = csr_timer1_status_clr;
      compat_timer_status_clr_vec[1] = compat_timer1_status_clr;
    end
  end

  assign timer_status_clr = csr_timer_status_clr_vec | compat_timer_status_clr_vec;

  genvar t;
  generate
    for (t = 0; t < TIMER_COUNT; t++) begin : gen_timer_mux
      assign timer_load_we[t] = csr_timer_load_we[t] | compat_timer_load_we[t];
      assign timer_load_wdata[t] = csr_timer_load_we[t] ? csr_timer_load_wdata[t] : compat_timer_load_wdata[t];
      assign timer_ctrl_we[t] = csr_timer_ctrl_we[t] | compat_timer_ctrl_we[t];
      assign timer_ctrl_wdata[t] = csr_timer_ctrl_we[t] ? csr_timer_ctrl_wdata[t] : compat_timer_ctrl_wdata[t];
    end
  endgenerate

  assign irq_clear = csr_irq_clear_pulse | compat_irq_clear_pulse;

endmodule : carbonio
