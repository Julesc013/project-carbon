// Project Carbon - Simulation BFM
// csr_bfm: Drives csr_if transactions.

module csr_bfm #(
    parameter int unsigned ADDR_W = 32,
    parameter int unsigned DATA_W = 32,
    parameter int unsigned PRIV_W = 2
) (
    input logic clk,
    input logic rst_n,
    csr_if.master csr
);
  initial begin
    csr.req_valid = 1'b0;
    csr.req_write = 1'b0;
    csr.req_addr  = '0;
    csr.req_wdata = '0;
    csr.req_wstrb = '0;
    csr.req_priv  = '0;
    csr.rsp_ready = 1'b0;
  end

  task automatic csr_write(
      input logic [ADDR_W-1:0] addr,
      input logic [DATA_W-1:0] data,
      input logic [(DATA_W/8)-1:0] wstrb,
      input logic [PRIV_W-1:0] priv,
      output logic fault
  );
    begin
      @(posedge clk);
      csr.req_valid <= 1'b1;
      csr.req_write <= 1'b1;
      csr.req_addr  <= addr;
      csr.req_wdata <= data;
      csr.req_wstrb <= wstrb;
      csr.req_priv  <= priv;
      while (!csr.req_ready) @(posedge clk);
      @(posedge clk);
      csr.req_valid <= 1'b0;

      csr.rsp_ready <= 1'b1;
      while (!csr.rsp_valid) @(posedge clk);
      fault = csr.rsp_fault;
      @(posedge clk);
      csr.rsp_ready <= 1'b0;
    end
  endtask

  task automatic csr_read(
      input logic [ADDR_W-1:0] addr,
      input logic [PRIV_W-1:0] priv,
      output logic [DATA_W-1:0] data,
      output logic fault
  );
    begin
      @(posedge clk);
      csr.req_valid <= 1'b1;
      csr.req_write <= 1'b0;
      csr.req_addr  <= addr;
      csr.req_wdata <= '0;
      csr.req_wstrb <= '0;
      csr.req_priv  <= priv;
      while (!csr.req_ready) @(posedge clk);
      @(posedge clk);
      csr.req_valid <= 1'b0;

      csr.rsp_ready <= 1'b1;
      while (!csr.rsp_valid) @(posedge clk);
      data = csr.rsp_rdata;
      fault = csr.rsp_fault;
      @(posedge clk);
      csr.rsp_ready <= 1'b0;
    end
  endtask

endmodule : csr_bfm

