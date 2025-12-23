// Project Carbon - Systems
// tier_host_ctrl: Minimal tier hosting controller for Option A personalities.

module tier_host_ctrl #(
    parameter logic [31:0] BASE_ADDR = 32'h0000_F300,
    parameter int unsigned STACK_DEPTH = carbon_arch_pkg::CARBON_MODESTACK_MIN_DEPTH,
    parameter int unsigned RESP_LATENCY = 0
) (
    input logic clk,
    input logic rst_n,
    fabric_if.slave bus,

    output logic [7:0] active_tier,
    output logic [1:0] active_core,
    output logic [3:0] core_halt_req,
    output logic [3:0] core_run_pulse
);
  import carbon_arch_pkg::*;

  localparam int unsigned CORE_COUNT = 4;
  localparam int unsigned FAB_ADDR_W = $bits(bus.req_addr);
  localparam int unsigned FAB_DATA_W = $bits(bus.req_wdata);
  localparam int unsigned FAB_STRB_W = $bits(bus.req_wstrb);
  localparam int unsigned FAB_OP_W   = $bits(bus.req_op);
  localparam int unsigned FAB_ID_W   = $bits(bus.req_id);
  localparam int unsigned FAB_CODE_W = $bits(bus.rsp_code);

  localparam logic [31:0] REQ_OFF      = 32'h0000_0000;
  localparam logic [31:0] STATUS_OFF   = 32'h0000_0004;
  localparam logic [31:0] ENTRY_LO_OFF = 32'h0000_0008;
  localparam logic [31:0] ENTRY_HI_OFF = 32'h0000_000c;
  localparam logic [31:0] CTRL_OFF     = 32'h0000_0010;

  localparam int unsigned SP_W = (STACK_DEPTH < 2) ? 1 : $clog2(STACK_DEPTH + 1);

  // Core identifiers.
  localparam logic [1:0] CORE_Z85  = 2'd0;
  localparam logic [1:0] CORE_Z90  = 2'd1;
  localparam logic [1:0] CORE_Z380 = 2'd2;
  localparam logic [1:0] CORE_Z480 = 2'd3;

  // Internal state.
  logic [7:0]  active_tier_q;
  logic [1:0]  active_core_q;
  logic [SP_W-1:0] sp_q;
  logic [7:0]  stack_tier_q [STACK_DEPTH];

  logic [31:0] entry_lo_q;
  logic [31:0] entry_hi_q;
  logic err_invalid_q;
  logic err_overflow_q;
  logic err_underflow_q;

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

  function automatic logic [1:0] tier_to_core(input logic [7:0] tier);
    begin
      if (tier <= 8'(CARBON_Z80_DERIVED_TIER_P2_Z80)) tier_to_core = CORE_Z85;
      else if (tier <= 8'(CARBON_Z80_DERIVED_TIER_P3_Z180)) tier_to_core = CORE_Z90;
      else if (tier <= 8'(CARBON_Z80_DERIVED_TIER_P6_Z380)) tier_to_core = CORE_Z380;
      else tier_to_core = CORE_Z480;
    end
  endfunction

  function automatic logic [FAB_DATA_W-1:0] read_word(input logic [FAB_ADDR_W-1:0] addr);
    logic [FAB_DATA_W-1:0] v;
    logic [31:0] off;
    begin
      v = '0;
      off = addr - BASE_ADDR;
      unique case (off)
        STATUS_OFF: begin
          v[7:0]   = active_tier_q;
          v[15:8]  = {{(8-SP_W){1'b0}}, sp_q};
          v[17:16] = active_core_q;
          v[24]    = err_invalid_q;
          v[25]    = err_overflow_q;
          v[26]    = err_underflow_q;
        end
        ENTRY_LO_OFF: v = entry_lo_q;
        ENTRY_HI_OFF: v = entry_hi_q;
        default: v = '0;
      endcase
      read_word = v;
    end
  endfunction

  task automatic write_wstrb32(
      inout logic [31:0] reg_q,
      input logic [31:0] data,
      input logic [FAB_STRB_W-1:0] wstrb
  );
    int unsigned b;
    begin
      for (b = 0; b < 4; b++) begin
        if (wstrb[b]) reg_q[(b*8)+:8] <= data[(b*8)+:8];
      end
    end
  endtask

  always_comb begin
    core_halt_req = 4'b1111;
    core_halt_req[active_core_q] = 1'b0;
  end

  assign active_tier = active_tier_q;
  assign active_core = active_core_q;

  // Main state machine.
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      active_tier_q <= 8'(CARBON_Z80_DERIVED_TIER_P0_I8080);
      active_core_q <= CORE_Z85;
      sp_q <= '0;
      entry_lo_q <= 32'h0;
      entry_hi_q <= 32'h0;
      err_invalid_q <= 1'b0;
      err_overflow_q <= 1'b0;
      err_underflow_q <= 1'b0;

      core_run_pulse <= 4'b0000;
      busy_q      <= 1'b0;
      delay_q     <= '0;
      rsp_valid_q <= 1'b0;
      rsp_rdata_q <= '0;
      rsp_code_q  <= '0;
      rsp_id_q    <= '0;
    end else begin
      logic [7:0] next_tier;
      logic [1:0] next_core;
      logic do_modeup;
      logic do_retmd;
      logic [7:0] req_byte0;
      logic [31:0] off;

      core_run_pulse <= 4'b0000;

      if (rsp_fire) rsp_valid_q <= 1'b0;

      if (busy_q && !rsp_valid_q) begin
        if (delay_q != 0) begin
          delay_q <= delay_q - 1'b1;
        end else begin
          rsp_valid_q <= 1'b1;
        end
      end

      next_tier = active_tier_q;
      next_core = active_core_q;
      do_modeup = 1'b0;
      do_retmd  = 1'b0;
      req_byte0 = 8'h00;
      off = 32'h0;

      if (req_fire) begin
        busy_q    <= 1'b1;
        delay_q   <= RESP_LATENCY;
        rsp_id_q  <= bus.req_id;
        rsp_rdata_q <= '0;
        rsp_code_q  <= FAB_CODE_W'(CARBON_FABRIC_RESP_OK);

        if (bus.req_op == FAB_OP_W'(CARBON_FABRIC_XACT_READ)) begin
          rsp_rdata_q <= read_word(bus.req_addr);
        end else if (bus.req_op == FAB_OP_W'(CARBON_FABRIC_XACT_WRITE)) begin
          off = bus.req_addr - BASE_ADDR;
          if (off == REQ_OFF) begin
            if (bus.req_wstrb[0]) begin
              req_byte0 = bus.req_wdata[7:0];
              if (req_byte0[7]) do_retmd = 1'b1;
              else do_modeup = 1'b1;
            end
          end else if (off == ENTRY_LO_OFF) begin
            write_wstrb32(entry_lo_q, bus.req_wdata, bus.req_wstrb);
          end else if (off == ENTRY_HI_OFF) begin
            write_wstrb32(entry_hi_q, bus.req_wdata, bus.req_wstrb);
          end else if (off == CTRL_OFF) begin
            if (bus.req_wstrb[0] && bus.req_wdata[0]) begin
              err_invalid_q <= 1'b0;
              err_overflow_q <= 1'b0;
              err_underflow_q <= 1'b0;
            end
          end else begin
            rsp_code_q <= FAB_CODE_W'(CARBON_FABRIC_RESP_DECODE_ERR);
          end
        end else begin
          rsp_code_q <= FAB_CODE_W'(CARBON_FABRIC_RESP_ACCESS_FAULT);
        end
      end

      if (do_modeup) begin
        if (req_byte0 <= active_tier_q) begin
          err_invalid_q <= 1'b1;
        end else if (sp_q == SP_W'(STACK_DEPTH)) begin
          err_overflow_q <= 1'b1;
        end else begin
          stack_tier_q[sp_q] <= active_tier_q;
          sp_q <= sp_q + 1'b1;
          next_tier = req_byte0;
          next_core = tier_to_core(req_byte0);
        end
      end else if (do_retmd) begin
        if (sp_q == 0) begin
          err_underflow_q <= 1'b1;
        end else begin
          sp_q <= sp_q - 1'b1;
          next_tier = stack_tier_q[sp_q - 1'b1];
          next_core = tier_to_core(stack_tier_q[sp_q - 1'b1]);
        end
      end

      if (next_core != active_core_q) begin
        core_run_pulse[next_core] <= 1'b1;
      end

      active_tier_q <= next_tier;
      active_core_q <= next_core;

      if (busy_q && rsp_fire) begin
        busy_q <= 1'b0;
      end
    end
  end

  wire _unused = ^{bus.req_size, bus.req_attr, entry_lo_q[0], entry_hi_q[0]};

endmodule : tier_host_ctrl
