// Project Carbon - Systems
// carbon_csr_master_simple: Small CSR master sequencer (single outstanding op).

module carbon_csr_master_simple (
    input logic clk,
    input logic rst_n,

    input  logic        start,
    input  logic        write,
    input  logic [31:0] addr,
    input  logic [31:0] wdata,
    input  logic [3:0]  wstrb,
    input  logic [1:0]  priv,

    output logic        busy,
    output logic        done_pulse,
    output logic        fault,
    output logic [31:0] rdata,

    csr_if.master csr
);
  localparam int unsigned CSR_ADDR_W = $bits(csr.req_addr);
  localparam int unsigned CSR_DATA_W = $bits(csr.req_wdata);
  localparam int unsigned CSR_STRB_W = $bits(csr.req_wstrb);
  localparam int unsigned CSR_PRIV_W = $bits(csr.req_priv);

  typedef enum logic [1:0] {ST_IDLE, ST_REQ, ST_RSP} st_e;
  st_e st_q;

  logic        req_write_q;
  logic [CSR_ADDR_W-1:0] req_addr_q;
  logic [CSR_DATA_W-1:0] req_wdata_q;
  logic [CSR_STRB_W-1:0] req_wstrb_q;
  logic [CSR_PRIV_W-1:0] req_priv_q;

  assign busy = (st_q != ST_IDLE);

  // Drive csr_if (hold stable under backpressure).
  assign csr.req_valid = (st_q == ST_REQ);
  assign csr.req_write = req_write_q;
  assign csr.req_addr  = req_addr_q;
  assign csr.req_wdata = req_wdata_q;
  assign csr.req_wstrb = req_wstrb_q;
  assign csr.req_priv  = req_priv_q;

  assign csr.rsp_ready = (st_q == ST_RSP);

  wire req_fire = csr.req_valid && csr.req_ready;
  wire rsp_fire = csr.rsp_valid && csr.rsp_ready;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      st_q       <= ST_IDLE;
      done_pulse <= 1'b0;
      fault      <= 1'b0;
      rdata      <= '0;
      req_write_q <= 1'b0;
      req_addr_q  <= '0;
      req_wdata_q <= '0;
      req_wstrb_q <= '0;
      req_priv_q  <= '0;
    end else begin
      done_pulse <= 1'b0;

      unique case (st_q)
        ST_IDLE: begin
          if (start) begin
            req_write_q <= write;
            req_addr_q  <= CSR_ADDR_W'(addr);
            req_wdata_q <= CSR_DATA_W'(wdata);
            req_wstrb_q <= CSR_STRB_W'(wstrb);
            req_priv_q  <= CSR_PRIV_W'(priv);
            st_q <= ST_REQ;
          end
        end
        ST_REQ: begin
          if (req_fire) begin
            st_q <= ST_RSP;
          end
        end
        default: begin
          if (rsp_fire) begin
            rdata <= csr.rsp_rdata;
            fault <= csr.rsp_fault;
            done_pulse <= 1'b1;
            st_q <= ST_IDLE;
          end
        end
      endcase
    end
  end

endmodule : carbon_csr_master_simple

