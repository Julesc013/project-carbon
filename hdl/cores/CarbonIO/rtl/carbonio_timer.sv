// Project Carbon - CarbonIO peripheral
// carbonio_timer: Monotonic tick + basic reloadable timers.

module carbonio_timer #(
    parameter int unsigned NUM_TIMERS = 2
) (
    input  logic clk,
    input  logic rst_n,
    input  logic enable,

    input  logic [NUM_TIMERS-1:0] load_we,
    input  logic [NUM_TIMERS-1:0][31:0] load_wdata,
    input  logic [NUM_TIMERS-1:0] ctrl_we,
    input  logic [NUM_TIMERS-1:0][31:0] ctrl_wdata,
    input  logic [NUM_TIMERS-1:0] status_clr,

    output logic [63:0] tick_counter,
    output logic [NUM_TIMERS-1:0][31:0] load_q,
    output logic [NUM_TIMERS-1:0][31:0] ctrl_q,
    output logic [NUM_TIMERS-1:0][31:0] value_q,
    output logic [NUM_TIMERS-1:0] expired_q,
    output logic [NUM_TIMERS-1:0] expired_pulse
);
  integer i;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      tick_counter <= 64'h0;
      for (i = 0; i < NUM_TIMERS; i++) begin
        load_q[i] <= 32'h0;
        ctrl_q[i] <= 32'h0;
        value_q[i] <= 32'h0;
        expired_q[i] <= 1'b0;
        expired_pulse[i] <= 1'b0;
      end
    end else begin
      expired_pulse <= '0;

      if (enable) begin
        tick_counter <= tick_counter + 64'd1;
      end

      for (i = 0; i < NUM_TIMERS; i++) begin
        if (load_we[i]) begin
          load_q[i] <= load_wdata[i];
        end
        if (ctrl_we[i]) begin
          ctrl_q[i][1:0] <= ctrl_wdata[i][1:0];
          if (ctrl_wdata[i][2]) begin
            value_q[i] <= load_q[i];
          end
        end
        if (status_clr[i]) begin
          expired_q[i] <= 1'b0;
        end

        if (enable && ctrl_q[i][0]) begin
          if (value_q[i] == 0) begin
            expired_q[i] <= 1'b1;
            expired_pulse[i] <= 1'b1;
            if (ctrl_q[i][1]) begin
              value_q[i] <= load_q[i];
            end else begin
              ctrl_q[i][0] <= 1'b0;
            end
          end else begin
            value_q[i] <= value_q[i] - 1'b1;
          end
        end
      end
    end
  end

endmodule : carbonio_timer
