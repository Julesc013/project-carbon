// Project Carbon - Common Infrastructure
// trace_ring: Generic trace record ring buffer.
//
// Records are written via a ready/valid stream and read out via a CSR window.

module trace_ring #(
    parameter int unsigned REC_W = 128,
    parameter int unsigned DEPTH = 16,
    parameter int unsigned CSR_DATA_W = 32
) (
    input logic clk,
    input logic rst_n,

    csr_if.slave csr,

    input  logic             trace_valid,
    output logic             trace_ready,
    input  logic [REC_W-1:0] trace_data
);
  import carbon_arch_pkg::*;

  localparam int unsigned PTR_W = (DEPTH <= 1) ? 1 : $clog2(DEPTH);
  localparam int unsigned CNT_W = $clog2(DEPTH + 1);
  localparam int unsigned WORDS_PER_REC = (REC_W + 31) / 32;

  // Implementation-defined CSR window (starts at CARBON_CSR_TRACE_CTL).
  localparam logic [31:0] ADDR_CTRL   = CARBON_CSR_TRACE_CTL;
  localparam logic [31:0] ADDR_STATUS = CARBON_CSR_TRACE_CTL + 32'h1;
  localparam logic [31:0] ADDR_DATA0  = CARBON_CSR_TRACE_CTL + 32'h4;
  localparam logic [31:0] ADDR_DATA1  = CARBON_CSR_TRACE_CTL + 32'h5;
  localparam logic [31:0] ADDR_DATA2  = CARBON_CSR_TRACE_CTL + 32'h6;
  localparam logic [31:0] ADDR_DATA3  = CARBON_CSR_TRACE_CTL + 32'h7;

  logic enable_q;

  logic [REC_W-1:0] mem [DEPTH];
  logic [PTR_W-1:0] wr_ptr_q, rd_ptr_q;
  logic [CNT_W-1:0] count_q;

  logic             rd_latch_valid_q;
  logic [REC_W-1:0] rd_latch_q;

  function automatic logic [PTR_W-1:0] inc_ptr(input logic [PTR_W-1:0] ptr);
    if (ptr == PTR_W'(DEPTH - 1)) inc_ptr = '0;
    else inc_ptr = ptr + 1'b1;
  endfunction

  assign trace_ready = enable_q && (count_q < CNT_W'(DEPTH));
  wire push_fire = trace_valid && trace_ready;

  // CSR response registers (single outstanding transaction).
  logic                   rsp_valid_q;
  logic [CSR_DATA_W-1:0]  rsp_rdata_q;
  logic                   rsp_fault_q;
  logic                   rsp_side_q;

  assign csr.req_ready       = !rsp_valid_q;
  assign csr.rsp_valid       = rsp_valid_q;
  assign csr.rsp_rdata       = rsp_rdata_q;
  assign csr.rsp_fault       = rsp_fault_q;
  assign csr.rsp_side_effect = rsp_side_q;

  function automatic logic [31:0] word32(input logic [REC_W-1:0] rec, input int unsigned word_idx);
    logic [31:0] w;
    begin
      w = 32'h0;
      if (word_idx < WORDS_PER_REC) begin
        w = rec[(word_idx*32) +: 32];
      end
      word32 = w;
    end
  endfunction

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      enable_q          <= 1'b0;
      wr_ptr_q          <= '0;
      rd_ptr_q          <= '0;
      count_q           <= '0;
      rd_latch_valid_q  <= 1'b0;
      rd_latch_q        <= '0;
      rsp_valid_q       <= 1'b0;
      rsp_rdata_q       <= '0;
      rsp_fault_q       <= 1'b0;
      rsp_side_q        <= 1'b0;
    end else begin
      // Push trace records
      if (push_fire) begin
        mem[wr_ptr_q] <= trace_data;
        wr_ptr_q      <= inc_ptr(wr_ptr_q);
        if (count_q < CNT_W'(DEPTH)) begin
          count_q <= count_q + 1'b1;
        end
      end

      // CSR response lifecycle
      if (rsp_valid_q && csr.rsp_ready) begin
        rsp_valid_q <= 1'b0;
      end

      if (csr.req_valid && csr.req_ready) begin
        rsp_valid_q <= 1'b1;
        rsp_fault_q <= 1'b0;
        rsp_side_q  <= csr.req_write;
        rsp_rdata_q <= '0;

        unique case (csr.req_addr)
          ADDR_CTRL: begin
            if (csr.req_write) begin
              // bit0=enable, bit1=clear (write 1 clears buffer)
              enable_q <= csr.req_wdata[0];
              if (csr.req_wdata[1]) begin
                wr_ptr_q         <= '0;
                rd_ptr_q         <= '0;
                count_q          <= '0;
                rd_latch_valid_q <= 1'b0;
              end
            end else begin
              rsp_rdata_q[0] <= enable_q;
              rsp_rdata_q[8 +: CNT_W] <= count_q;
              rsp_rdata_q[31] <= rd_latch_valid_q;
            end
          end

          ADDR_STATUS: begin
            if (!csr.req_write) begin
              rsp_rdata_q[0] <= (count_q != '0);
              rsp_rdata_q[1] <= (count_q == CNT_W'(DEPTH));
              rsp_rdata_q[8 +: CNT_W] <= count_q;
            end else begin
              rsp_fault_q <= 1'b1;
            end
          end

          ADDR_DATA0: begin
            if (csr.req_write) begin
              rsp_fault_q <= 1'b1;
            end else begin
              if (!rd_latch_valid_q) begin
                if (count_q != '0) begin
                  rd_latch_q       <= mem[rd_ptr_q];
                  rd_latch_valid_q <= 1'b1;
                  rd_ptr_q         <= inc_ptr(rd_ptr_q);
                  count_q          <= count_q - 1'b1;
                end else begin
                  rsp_fault_q <= 1'b1;
                end
              end
              rsp_rdata_q <= word32(rd_latch_valid_q ? rd_latch_q : mem[rd_ptr_q], 0);
            end
          end

          ADDR_DATA1: begin
            if (!csr.req_write && rd_latch_valid_q) rsp_rdata_q <= word32(rd_latch_q, 1);
            else rsp_fault_q <= 1'b1;
          end
          ADDR_DATA2: begin
            if (!csr.req_write && rd_latch_valid_q) rsp_rdata_q <= word32(rd_latch_q, 2);
            else rsp_fault_q <= 1'b1;
          end
          ADDR_DATA3: begin
            if (!csr.req_write && rd_latch_valid_q) begin
              rsp_rdata_q <= word32(rd_latch_q, 3);
              rd_latch_valid_q <= 1'b0;
            end else begin
              rsp_fault_q <= 1'b1;
            end
          end

          default: begin
            rsp_fault_q <= 1'b1;
          end
        endcase
      end
    end
  end

endmodule : trace_ring

