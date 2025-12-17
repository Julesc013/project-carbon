// Project Carbon - Systems
// carbon_mmio_regs: Minimal MMIO block (signature + poweroff + UART-like TX).

module carbon_mmio_regs #(
    parameter logic [31:0] BASE_ADDR = 32'h0000_0000,
    parameter logic [31:0] SIGNATURE_RESET = 32'h0000_0000,
    parameter int unsigned RESP_LATENCY = 1
) (
    input logic clk,
    input logic rst_n,
    fabric_if.slave bus,

    output logic [31:0] signature,
    output logic        poweroff,
    output logic        uart_tx_valid,
    output logic [7:0]  uart_tx_byte
);
  import carbon_arch_pkg::*;
  import carbon_memmap_pkg::*;

  localparam int unsigned FAB_ADDR_W = $bits(bus.req_addr);
  localparam int unsigned FAB_DATA_W = $bits(bus.req_wdata);
  localparam int unsigned FAB_STRB_W = $bits(bus.req_wstrb);
  localparam int unsigned FAB_OP_W   = $bits(bus.req_op);
  localparam int unsigned FAB_ID_W   = $bits(bus.req_id);
  localparam int unsigned FAB_CODE_W = $bits(bus.rsp_code);

  localparam int unsigned BYTES_PER_WORD = (FAB_DATA_W / 8);

  // State
  logic [31:0] signature_q;
  logic poweroff_q;

  // Pulse-type output (UART TX)
  logic uart_tx_valid_q;
  logic [7:0] uart_tx_byte_q;

  assign signature     = signature_q;
  assign poweroff      = poweroff_q;
  assign uart_tx_valid = uart_tx_valid_q;
  assign uart_tx_byte  = uart_tx_byte_q;

  // Single outstanding transaction.
  logic busy_q;
  logic [31:0] delay_q;

  // Response registers.
  logic                 rsp_valid_q;
  logic [FAB_DATA_W-1:0] rsp_rdata_q;
  logic [FAB_CODE_W-1:0] rsp_code_q;
  logic [FAB_ID_W-1:0]   rsp_id_q;

  assign bus.req_ready = !busy_q;
  assign bus.rsp_valid = rsp_valid_q;
  assign bus.rsp_rdata = rsp_rdata_q;
  assign bus.rsp_code  = rsp_code_q;
  assign bus.rsp_id    = rsp_id_q;

  wire req_fire = bus.req_valid && bus.req_ready;
  wire rsp_fire = bus.rsp_valid && bus.rsp_ready;

  function automatic logic [7:0] mmio_read_byte(input int signed off);
    logic [7:0] b;
    begin
      b = 8'h00;
      if ((off >= 0) && (off < 4)) begin
        b = signature_q[(off*8)+:8];
      end else if ((off >= 4) && (off < 8)) begin
        b = {7'h0, poweroff_q};
      end else if (off == 8) begin
        b = uart_tx_byte_q;
      end
      mmio_read_byte = b;
    end
  endfunction

  function automatic logic [FAB_DATA_W-1:0] mmio_read_word(input logic [FAB_ADDR_W-1:0] addr);
    logic [FAB_DATA_W-1:0] v;
    int signed a0;
    int signed ai;
    int unsigned b;
    begin
      v  = '0;
      a0 = int'(addr) - int'(BASE_ADDR);
      for (b = 0; b < BYTES_PER_WORD; b++) begin
        ai = a0 + int'(b);
        v[(b*8)+:8] = mmio_read_byte(ai);
      end
      mmio_read_word = v;
    end
  endfunction

  task automatic mmio_write_bytes(
      input logic [FAB_ADDR_W-1:0] addr,
      input logic [FAB_DATA_W-1:0] data,
      input logic [FAB_STRB_W-1:0] wstrb
  );
    int signed a0;
    int signed ai;
    int unsigned b;
    begin
      a0 = int'(addr) - int'(BASE_ADDR);
      for (b = 0; b < BYTES_PER_WORD; b++) begin
        if (!wstrb[b]) continue;
        ai = a0 + int'(b);

        // Signature bytes 0..3
        if ((ai >= 0) && (ai < 4)) begin
          signature_q[(ai*8)+:8] <= data[(b*8)+:8];
        end

        // Poweroff latch (any byte within 4..7 triggers).
        if ((ai >= 4) && (ai < 8)) begin
          poweroff_q <= 1'b1;
        end

        // UART TX byte (byte offset 8)
        if (ai == 8) begin
          uart_tx_valid_q <= 1'b1;
          uart_tx_byte_q  <= data[(b*8)+:8];
        end
      end
    end
  endtask

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      signature_q     <= SIGNATURE_RESET;
      poweroff_q      <= 1'b0;
      uart_tx_valid_q <= 1'b0;
      uart_tx_byte_q  <= 8'h00;

      busy_q      <= 1'b0;
      delay_q     <= '0;
      rsp_valid_q <= 1'b0;
      rsp_rdata_q <= '0;
      rsp_code_q  <= '0;
      rsp_id_q    <= '0;
    end else begin
      // One-cycle pulse
      uart_tx_valid_q <= 1'b0;

      if (rsp_fire) rsp_valid_q <= 1'b0;

      if (busy_q && !rsp_valid_q) begin
        if (delay_q != 0) begin
          delay_q <= delay_q - 1'b1;
        end else begin
          rsp_valid_q <= 1'b1;
        end
      end

      if (req_fire) begin
        busy_q   <= 1'b1;
        delay_q  <= RESP_LATENCY;
        rsp_id_q <= bus.req_id;

        rsp_rdata_q <= '0;
        rsp_code_q  <= FAB_CODE_W'(CARBON_FABRIC_RESP_OK);

        if (bus.req_op == FAB_OP_W'(CARBON_FABRIC_XACT_READ)) begin
          rsp_rdata_q <= mmio_read_word(bus.req_addr);
        end else if (bus.req_op == FAB_OP_W'(CARBON_FABRIC_XACT_WRITE)) begin
          mmio_write_bytes(bus.req_addr, bus.req_wdata, bus.req_wstrb);
        end else begin
          rsp_code_q <= FAB_CODE_W'(CARBON_FABRIC_RESP_ACCESS_FAULT);
        end
      end

      if (busy_q && rsp_fire) begin
        busy_q <= 1'b0;
      end
    end
  end

  wire _unused = ^{bus.req_size, bus.req_attr};

endmodule : carbon_mmio_regs

