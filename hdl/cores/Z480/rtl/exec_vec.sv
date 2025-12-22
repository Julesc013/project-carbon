// Project Carbon - Z480 P7 core scaffold
// exec_vec: Stub vector unit (v1: no real execute; reserves 128-bit vector path).

module exec_vec (
    input logic clk,
    input logic rst_n,

    input  logic flush,

    input  logic                      in_valid,
    input  z480_pkg::z480_uop_tagged_t in_uop,
    output logic                      in_ready,

    output logic           wb_valid,
    output z480_pkg::z480_wb_t wb,
    input  logic           wb_ready
);
  import z480_pkg::*;

  logic wb_valid_q;
  z480_wb_t wb_q;

  assign wb_valid = wb_valid_q;
  assign wb       = wb_q;
  assign in_ready = !wb_valid_q || wb_ready;

  wire accept = in_valid && in_ready && !flush;
  wire retire = wb_valid_q && wb_ready;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      wb_valid_q <= 1'b0;
      wb_q <= '0;
    end else begin
      if (flush) begin
        wb_valid_q <= 1'b0;
      end else begin
        unique case ({accept, retire})
          2'b10: begin
            wb_valid_q <= 1'b1;
            wb_q.rob_idx   <= in_uop.rob_idx;
            wb_q.prd_valid <= in_uop.uop.uop.rd_valid;
            wb_q.prd       <= in_uop.uop.prd;
            wb_q.value     <= 64'h0;
            wb_q.flags     <= 32'h0;
          end
          2'b01: wb_valid_q <= 1'b0;
          2'b11: begin
            wb_valid_q <= 1'b1;
            wb_q.rob_idx   <= in_uop.rob_idx;
            wb_q.prd_valid <= in_uop.uop.uop.rd_valid;
            wb_q.prd       <= in_uop.uop.prd;
            wb_q.value     <= 64'h0;
            wb_q.flags     <= 32'h0;
          end
          default: begin
          end
        endcase
      end
    end
  end

endmodule : exec_vec
