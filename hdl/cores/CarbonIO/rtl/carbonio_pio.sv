// Project Carbon - CarbonIO peripheral
// carbonio_pio: Parallel I/O block with edge capture FIFO and simple filters.

module carbonio_pio #(
    parameter int unsigned WIDTH = 32,
    parameter int unsigned EDGE_FIFO_DEPTH = 16
) (
    input  logic clk,
    input  logic rst_n,
    input  logic enable,

    input  logic [WIDTH-1:0] pio_in,
    output logic [WIDTH-1:0] pio_out,
    output logic [WIDTH-1:0] pio_dir,

    input  logic out_we,
    input  logic [WIDTH-1:0] out_wdata,
    input  logic dir_we,
    input  logic [WIDTH-1:0] dir_wdata,

    input  logic filter_we,
    input  logic [7:0] filter_len_wdata,
    input  logic match_we,
    input  logic [WIDTH-1:0] match_value_wdata,
    input  logic [WIDTH-1:0] match_mask_wdata,

    input  logic edge_pop,
    output logic [WIDTH-1:0] edge_data,
    output logic [$clog2(EDGE_FIFO_DEPTH+1)-1:0] edge_count,
    output logic edge_overflow,
    output logic match_pulse,
    output logic edge_pulse,

    output logic [7:0] filter_len,
    output logic [WIDTH-1:0] match_value,
    output logic [WIDTH-1:0] match_mask
);
  logic [WIDTH-1:0] pio_out_q;
  logic [WIDTH-1:0] pio_dir_q;
  logic [7:0] filter_len_q;
  logic [WIDTH-1:0] match_value_q;
  logic [WIDTH-1:0] match_mask_q;

  assign pio_out = pio_out_q;
  assign pio_dir = pio_dir_q;
  assign filter_len = filter_len_q;
  assign match_value = match_value_q;
  assign match_mask = match_mask_q;

  // Edge capture FIFO.
  logic edge_full;
  logic edge_empty;
  logic edge_push;

  carbonio_fifo #(
      .WIDTH(WIDTH),
      .DEPTH(EDGE_FIFO_DEPTH)
  ) u_edge_fifo (
      .clk(clk),
      .rst_n(rst_n),
      .push(edge_push),
      .push_data(pio_in),
      .pop(edge_pop),
      .pop_data(edge_data),
      .full(edge_full),
      .empty(edge_empty),
      .count(edge_count)
  );

  // Simple glitch filter + edge detection.
  logic [WIDTH-1:0] pio_stable_q;
  logic [WIDTH-1:0] candidate_q;
  logic [7:0] filter_cnt_q;
  logic filter_pending_q;

  logic match_last_q;

  assign edge_overflow = edge_overflow_q;
  logic edge_overflow_q;

  assign edge_pulse = edge_push;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      pio_out_q <= '0;
      pio_dir_q <= '0;
      filter_len_q <= 8'h0;
      match_value_q <= '0;
      match_mask_q <= '0;

      pio_stable_q <= '0;
      candidate_q <= '0;
      filter_cnt_q <= 8'h0;
      filter_pending_q <= 1'b0;
      edge_push <= 1'b0;
      match_pulse <= 1'b0;
      edge_overflow_q <= 1'b0;
      match_last_q <= 1'b0;
    end else begin
      if (out_we) pio_out_q <= out_wdata;
      if (dir_we) pio_dir_q <= dir_wdata;
      if (filter_we) filter_len_q <= filter_len_wdata;
      if (match_we) begin
        match_value_q <= match_value_wdata;
        match_mask_q  <= match_mask_wdata;
      end

      edge_push <= 1'b0;
      match_pulse <= 1'b0;

      if (!enable) begin
        filter_pending_q <= 1'b0;
      end else begin
        if (!filter_pending_q) begin
          if (pio_in != pio_stable_q) begin
            if (filter_len_q == 0) begin
              pio_stable_q <= pio_in;
              edge_push <= 1'b1;
            end else begin
              candidate_q <= pio_in;
              filter_cnt_q <= filter_len_q;
              filter_pending_q <= 1'b1;
            end
          end
        end else begin
          if (pio_in != candidate_q) begin
            candidate_q <= pio_in;
            filter_cnt_q <= filter_len_q;
          end else if (filter_cnt_q == 0) begin
            pio_stable_q <= candidate_q;
            edge_push <= 1'b1;
            filter_pending_q <= 1'b0;
          end else begin
            filter_cnt_q <= filter_cnt_q - 1'b1;
          end
        end

        if (((pio_stable_q & match_mask_q) == (match_value_q & match_mask_q)) && !match_last_q) begin
          match_pulse <= 1'b1;
          match_last_q <= 1'b1;
        end else if ((pio_stable_q & match_mask_q) != (match_value_q & match_mask_q)) begin
          match_last_q <= 1'b0;
        end
      end

      if (edge_push && edge_full) begin
        edge_overflow_q <= 1'b1;
      end
    end
  end

endmodule : carbonio_pio
