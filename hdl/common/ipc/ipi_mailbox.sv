// Project Carbon - Common Infrastructure
// ipi_mailbox: Per-core mailbox RX FIFOs with IPI indication.
//
// Each core has its own CSR port. A core sends by:
// - Programming its SEND_MASK.
// - Writing TX_DATA (one word), which is delivered to selected targets' RX FIFOs.
//
// RX_DATA reads pop one word from the local RX FIFO.
//
// Notes:
// - In v1, multiple simultaneous TX writes are accepted only if their target sets
//   do not overlap (deterministic low-index sender priority otherwise via backpressure).

module ipi_mailbox #(
    parameter int unsigned CORES = 2,
    parameter int unsigned DATA_W = 32,
    parameter int unsigned FIFO_DEPTH = 4
) (
    input logic clk,
    input logic rst_n,

    csr_if.slave csr [CORES],

    output logic [CORES-1:0] ipi_irq
);
  localparam int unsigned ADDR_SEL_W = 2; // word index from addr[3:2]
  localparam int unsigned SEL_SEND_MASK = 0;
  localparam int unsigned SEL_TX_DATA   = 1;
  localparam int unsigned SEL_RX_DATA   = 2;
  localparam int unsigned SEL_STATUS    = 3;

  // Per-core send mask register.
  logic [CORES-1:0] send_mask_q [CORES];

  // Per-core CSR response registers.
  logic               rsp_valid_q [CORES];
  logic [DATA_W-1:0]  rsp_rdata_q [CORES];
  logic               rsp_fault_q [CORES];
  logic               rsp_side_q  [CORES];

  // RX FIFO signals.
  logic                rx_push_valid [CORES];
  logic                rx_push_ready [CORES];
  logic [DATA_W-1:0]   rx_push_data  [CORES];
  logic                rx_pop_valid  [CORES];
  logic                rx_pop_ready  [CORES];
  logic [DATA_W-1:0]   rx_pop_data   [CORES];
  logic                rx_afull      [CORES];
  logic                rx_aempty     [CORES];

  genvar g;
  generate
    for (g = 0; g < CORES; g++) begin : g_fifo
      mailbox_fifo #(
          .WIDTH(DATA_W),
          .DEPTH(FIFO_DEPTH)
      ) u_rx_fifo (
          .clk(clk),
          .rst_n(rst_n),
          .push_valid(rx_push_valid[g]),
          .push_ready(rx_push_ready[g]),
          .push_data(rx_push_data[g]),
          .pop_valid(rx_pop_valid[g]),
          .pop_ready(rx_pop_ready[g]),
          .pop_data(rx_pop_data[g]),
          .almost_full(rx_afull[g]),
          .almost_empty(rx_aempty[g])
      );
      assign ipi_irq[g] = rx_pop_valid[g];
    end
  endgenerate

  integer i, j;
  logic [CORES-1:0] tx_req;
  logic [CORES-1:0] tx_accept;
  logic [CORES-1:0] rx_claimed;

  // Default combinational driving for FIFO handshakes.
  always_comb begin
    for (j = 0; j < int'(CORES); j++) begin
      rx_push_valid[j] = 1'b0;
      rx_push_data[j]  = '0;
      rx_pop_ready[j]  = 1'b0;
    end

    // Identify TX requests and choose an acceptance set that does not overlap targets.
    tx_req    = '0;
    tx_accept = '0;
    rx_claimed = '0;

    for (i = 0; i < int'(CORES); i++) begin
      if (!rsp_valid_q[i]) begin
        if (csr[i].req_valid && csr[i].req_write && (csr[i].req_addr[3:2] == ADDR_SEL_W'(SEL_TX_DATA))) begin
          tx_req[i] = 1'b1;
        end
      end
    end

    for (i = 0; i < int'(CORES); i++) begin
      logic can_send;
      can_send = tx_req[i];

      // Require all targeted RX FIFOs to be ready, and not already claimed.
      for (j = 0; j < int'(CORES); j++) begin
        if (send_mask_q[i][j]) begin
          if (!rx_push_ready[j]) begin
            can_send = 1'b0;
          end
          if (rx_claimed[j]) begin
            can_send = 1'b0;
          end
        end
      end

      if (can_send) begin
        tx_accept[i] = 1'b1;
        rx_claimed  |= send_mask_q[i];
      end
    end

    // Drive RX FIFO pushes for accepted TX writes.
    for (j = 0; j < int'(CORES); j++) begin
      for (i = 0; i < int'(CORES); i++) begin
        if (tx_accept[i] && send_mask_q[i][j]) begin
          rx_push_valid[j] = 1'b1;
          rx_push_data[j]  = csr[i].req_wdata;
        end
      end
    end

    // Drive RX FIFO pops when RX_DATA is read and accepted.
    for (i = 0; i < int'(CORES); i++) begin
      if (!rsp_valid_q[i]) begin
        if (csr[i].req_valid && !csr[i].req_write && (csr[i].req_addr[3:2] == ADDR_SEL_W'(SEL_RX_DATA))) begin
          rx_pop_ready[i] = csr[i].req_ready;
        end
      end
    end
  end

  // CSR ready/response wiring.
  generate
    for (g = 0; g < CORES; g++) begin : g_csr
      assign csr[g].req_ready       = !rsp_valid_q[g] && (!tx_req[g] || tx_accept[g]);
      assign csr[g].rsp_valid       = rsp_valid_q[g];
      assign csr[g].rsp_rdata       = rsp_rdata_q[g];
      assign csr[g].rsp_fault       = rsp_fault_q[g];
      assign csr[g].rsp_side_effect = rsp_side_q[g];
    end
  endgenerate

  // Sequential state and CSR response generation.
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      for (i = 0; i < int'(CORES); i++) begin
        send_mask_q[i] <= '0;
        rsp_valid_q[i] <= 1'b0;
        rsp_rdata_q[i] <= '0;
        rsp_fault_q[i] <= 1'b0;
        rsp_side_q[i]  <= 1'b0;
      end
    end else begin
      for (i = 0; i < int'(CORES); i++) begin
        if (rsp_valid_q[i] && csr[i].rsp_ready) begin
          rsp_valid_q[i] <= 1'b0;
        end

        if (csr[i].req_valid && csr[i].req_ready) begin
          rsp_valid_q[i] <= 1'b1;
          rsp_fault_q[i] <= 1'b0;
          rsp_side_q[i]  <= csr[i].req_write;
          rsp_rdata_q[i] <= '0;

          unique case (csr[i].req_addr[3:2])
            ADDR_SEL_W'(SEL_SEND_MASK): begin
              if (csr[i].req_write) begin
                send_mask_q[i] <= csr[i].req_wdata[CORES-1:0];
              end else begin
                rsp_rdata_q[i] <= {{(DATA_W-CORES){1'b0}}, send_mask_q[i]};
              end
            end
            ADDR_SEL_W'(SEL_TX_DATA): begin
              // TX_DATA write is accepted only when tx_accept[i] is true (else backpressured).
              if (!csr[i].req_write) begin
                rsp_fault_q[i] <= 1'b1;
              end
            end
            ADDR_SEL_W'(SEL_RX_DATA): begin
              if (csr[i].req_write) begin
                rsp_fault_q[i] <= 1'b1;
              end else begin
                if (rx_pop_valid[i]) begin
                  rsp_rdata_q[i] <= rx_pop_data[i];
                end else begin
                  rsp_fault_q[i] <= 1'b1;
                  rsp_rdata_q[i] <= '0;
                end
              end
            end
            ADDR_SEL_W'(SEL_STATUS): begin
              if (!csr[i].req_write) begin
                rsp_rdata_q[i][0] <= rx_pop_valid[i];
                rsp_rdata_q[i][1] <= rx_afull[i];
                rsp_rdata_q[i][2] <= rx_aempty[i];
              end else begin
                rsp_fault_q[i] <= 1'b1;
              end
            end
            default: begin
              rsp_fault_q[i] <= 1'b1;
            end
          endcase
        end
      end
    end
  end

endmodule : ipi_mailbox

