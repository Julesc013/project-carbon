// Project Carbon - CarbonIO peripheral
// carbonio_uart: FIFO-based UART datapath (register-level).

module carbonio_uart #(
    parameter int unsigned RX_DEPTH = 64,
    parameter int unsigned TX_DEPTH = 64
) (
    input  logic clk,
    input  logic rst_n,

    input  logic enable,
    input  logic ts_enable,
    input  logic [63:0] tick_counter,
    input  logic clear_errors,

    // External RX push (from a serial frontend or testbench).
    input  logic       rx_push,
    input  logic [7:0] rx_data,
    output logic       rx_ready,

    // External TX consume.
    input  logic       uart_tx_ready,
    output logic       uart_tx_valid,
    output logic [7:0] uart_tx_data,

    // CSR/compat access.
    input  logic       rx_pop,
    output logic [7:0] rx_data_out,
    input  logic       tx_push,
    input  logic [7:0] tx_data,

    output logic [$clog2(RX_DEPTH+1)-1:0] rx_count,
    output logic [$clog2(TX_DEPTH+1)-1:0] tx_count,
    output logic rx_overflow,
    output logic tx_overflow,
    output logic [63:0] rx_timestamp
);
  logic rx_full;
  logic rx_empty;
  logic tx_full;
  logic tx_empty;

  logic rx_push_ok;
  logic rx_pop_ok;
  logic tx_push_ok;
  logic tx_pop_ok;

  carbonio_fifo #(
      .WIDTH(8),
      .DEPTH(RX_DEPTH)
  ) u_rx_fifo (
      .clk(clk),
      .rst_n(rst_n),
      .push(rx_push_ok),
      .push_data(rx_data),
      .pop(rx_pop_ok),
      .pop_data(rx_data_out),
      .full(rx_full),
      .empty(rx_empty),
      .count(rx_count)
  );

  logic [7:0] tx_pop_data;
  carbonio_fifo #(
      .WIDTH(8),
      .DEPTH(TX_DEPTH)
  ) u_tx_fifo (
      .clk(clk),
      .rst_n(rst_n),
      .push(tx_push_ok),
      .push_data(tx_data),
      .pop(tx_pop_ok),
      .pop_data(tx_pop_data),
      .full(tx_full),
      .empty(tx_empty),
      .count(tx_count)
  );

  assign rx_ready = enable && !rx_full;
  assign rx_push_ok = rx_push && rx_ready;
  assign rx_pop_ok = rx_pop && enable && !rx_empty;

  assign tx_push_ok = tx_push && enable && !tx_full;
  assign tx_pop_ok = enable && uart_tx_ready && !tx_empty;

  assign uart_tx_valid = tx_pop_ok;
  assign uart_tx_data = tx_pop_data;

  logic rx_overflow_q;
  logic tx_overflow_q;
  logic [63:0] rx_ts_q;

  assign rx_overflow = rx_overflow_q;
  assign tx_overflow = tx_overflow_q;
  assign rx_timestamp = rx_ts_q;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      rx_overflow_q <= 1'b0;
      tx_overflow_q <= 1'b0;
      rx_ts_q <= 64'h0;
    end else begin
      if (clear_errors) begin
        rx_overflow_q <= 1'b0;
        tx_overflow_q <= 1'b0;
      end

      if (rx_push && !rx_ready) begin
        rx_overflow_q <= 1'b1;
      end
      if (tx_push && tx_full) begin
        tx_overflow_q <= 1'b1;
      end

      if (rx_push_ok && ts_enable) begin
        rx_ts_q <= tick_counter;
      end
    end
  end

endmodule : carbonio_uart
