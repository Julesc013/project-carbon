// Project Carbon - Common Infrastructure
// fabric_arbiter_mxn: Basic round-robin arbiter for M masters to N slaves.
//
// Simplicity/correctness constraints (v1):
// - At most one in-flight transaction per slave.
// - At most one in-flight transaction per master.
// - Requests are held stable under backpressure via a per-slave lock.

module fabric_arbiter_mxn #(
    parameter int unsigned M = 2,
    parameter int unsigned N = 1,
    parameter int unsigned ADDR_W = 32,
    parameter int unsigned DATA_W = 32,
    parameter int unsigned ID_W   = 4,
    parameter int unsigned OP_W   = 8,
    parameter int unsigned SIZE_W = 3,
    parameter int unsigned ATTR_W = carbon_arch_pkg::CARBON_FABRIC_ATTR_WIDTH_BITS,
    parameter int unsigned CODE_W = 8,

    parameter bit HAS_DEFAULT = 1'b1,
    parameter int unsigned DEFAULT_SLAVE = 0,
    parameter logic [N*ADDR_W-1:0] SLAVE_BASE = '0,
    parameter logic [N*ADDR_W-1:0] SLAVE_MASK = '0
) (
    input logic clk,
    input logic rst_n,
    fabric_if #(
        .ADDR_W(ADDR_W),
        .DATA_W(DATA_W),
        .ID_W(ID_W),
        .OP_W(OP_W),
        .SIZE_W(SIZE_W),
        .ATTR_W(ATTR_W),
        .CODE_W(CODE_W)
    ).slave masters [M],
    fabric_if #(
        .ADDR_W(ADDR_W),
        .DATA_W(DATA_W),
        .ID_W(ID_W),
        .OP_W(OP_W),
        .SIZE_W(SIZE_W),
        .ATTR_W(ATTR_W),
        .CODE_W(CODE_W)
    ).master slaves [N]
);
  import carbon_arch_pkg::*;

  localparam int unsigned M_W = (M <= 1) ? 1 : $clog2(M);
  localparam int unsigned N_W = (N <= 1) ? 1 : $clog2(N);

  // Per-master decode result
  logic             dec_err [M];
  logic [N_W-1:0]   dec_idx [M];

  genvar gi;
  generate
    for (gi = 0; gi < M; gi++) begin : g_decode
      fabric_addr_decode #(
          .N(N),
          .ADDR_W(ADDR_W),
          .HAS_DEFAULT(HAS_DEFAULT),
          .DEFAULT_SLAVE(DEFAULT_SLAVE),
          .SLAVE_BASE(SLAVE_BASE),
          .SLAVE_MASK(SLAVE_MASK)
      ) u_dec (
          .addr(masters[gi].req_addr),
          .hit(),
          .decode_err(dec_err[gi]),
          .slave_idx(dec_idx[gi])
      );
    end
  endgenerate

  // Per-slave request lock and in-flight tracking
  logic           lock_q      [N];
  logic [M_W-1:0] lock_m_q    [N];
  logic           inflight_q  [N];
  logic [M_W-1:0] resp_m_q    [N];
  logic [M_W-1:0] rr_ptr_q    [N];

  // Per-master error response bookkeeping (decode_err injections)
  logic           err_pending_q [M];
  logic [ID_W-1:0] err_id_q     [M];

  // Per-master busy flag (at most one outstanding).
  logic busy_q [M];

  function automatic int unsigned pick_rr(
      input int unsigned start,
      input logic [M-1:0] req_vec
  );
    int unsigned k;
    int unsigned idx;
    begin
      pick_rr = M;
      for (k = 0; k < int'(M); k++) begin
        idx = (start + k) % int'(M);
        if (req_vec[idx]) begin
          pick_rr = idx;
          break;
        end
      end
    end
  endfunction

  // Combinational wiring for masters/slaves
  integer m, s;
  logic [M-1:0] locked_for_master;
  logic [M-1:0] responding_from_slave;
  logic [N-1:0] slave_targets_master [M];

  always_comb begin
    // Default all outputs to idle/backpressure.
    for (m = 0; m < int'(M); m++) begin
      masters[m].req_ready = 1'b0;
      masters[m].rsp_valid = 1'b0;
      masters[m].rsp_rdata = '0;
      masters[m].rsp_code  = '0;
      masters[m].rsp_id    = '0;
    end
    for (s = 0; s < int'(N); s++) begin
      slaves[s].req_valid = 1'b0;
      slaves[s].req_op    = '0;
      slaves[s].req_addr  = '0;
      slaves[s].req_wdata = '0;
      slaves[s].req_wstrb = '0;
      slaves[s].req_size  = '0;
      slaves[s].req_attr  = '0;
      slaves[s].req_id    = '0;
      slaves[s].rsp_ready = 1'b0;
    end

    locked_for_master = '0;
    responding_from_slave = '0;
    for (m = 0; m < int'(M); m++) begin
      slave_targets_master[m] = '0;
    end

    // Mark which master is currently locked to a slave.
    for (s = 0; s < int'(N); s++) begin
      if (lock_q[s]) begin
        locked_for_master[lock_m_q[s]] = 1'b1;
      end
    end

    // Route responses: either injected decode_err per-master, or from a slave.
    for (m = 0; m < int'(M); m++) begin
      if (err_pending_q[m]) begin
        masters[m].rsp_valid = 1'b1;
        masters[m].rsp_rdata = '0;
        masters[m].rsp_code  = CODE_W'(CARBON_FABRIC_RESP_DECODE_ERR);
        masters[m].rsp_id    = err_id_q[m];
      end
    end

    for (s = 0; s < int'(N); s++) begin
      if (inflight_q[s]) begin
        m = int'(resp_m_q[s]);
        responding_from_slave[m] = 1'b1;
        slave_targets_master[m][s] = 1'b1;
        masters[m].rsp_valid = slaves[s].rsp_valid;
        masters[m].rsp_rdata = slaves[s].rsp_rdata;
        masters[m].rsp_code  = slaves[s].rsp_code;
        masters[m].rsp_id    = slaves[s].rsp_id;
        slaves[s].rsp_ready  = masters[m].rsp_ready;
      end
    end

    // Drive requests for locked slaves, and assign req_ready to their masters.
    for (s = 0; s < int'(N); s++) begin
      if (lock_q[s] && !inflight_q[s]) begin
        m = int'(lock_m_q[s]);
        slaves[s].req_valid = masters[m].req_valid;
        slaves[s].req_op    = masters[m].req_op;
        slaves[s].req_addr  = masters[m].req_addr;
        slaves[s].req_wdata = masters[m].req_wdata;
        slaves[s].req_wstrb = masters[m].req_wstrb;
        slaves[s].req_size  = masters[m].req_size;
        slaves[s].req_attr  = masters[m].req_attr;
        slaves[s].req_id    = masters[m].req_id;

        if (!busy_q[m] && !err_pending_q[m]) begin
          masters[m].req_ready = slaves[s].req_ready;
        end else begin
          masters[m].req_ready = 1'b0;
        end
      end
    end

    // Allow decode_err-only requests to be accepted immediately when not busy.
    for (m = 0; m < int'(M); m++) begin
      if (!locked_for_master[m] && !busy_q[m] && !err_pending_q[m]) begin
        if (masters[m].req_valid && dec_err[m]) begin
          masters[m].req_ready = 1'b1;
        end
      end
    end
  end

  // Sequential control state updates
  integer si;
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      for (si = 0; si < int'(N); si++) begin
        lock_q[si]     <= 1'b0;
        lock_m_q[si]   <= '0;
        inflight_q[si] <= 1'b0;
        resp_m_q[si]   <= '0;
        rr_ptr_q[si]   <= '0;
      end
      for (si = 0; si < int'(M); si++) begin
        err_pending_q[si] <= 1'b0;
        err_id_q[si]      <= '0;
        busy_q[si]        <= 1'b0;
      end
    end else begin
      // Handle injected decode_err responses per master.
      for (si = 0; si < int'(M); si++) begin
        if (!busy_q[si] && !err_pending_q[si]) begin
          if (masters[si].req_valid && masters[si].req_ready && dec_err[si]) begin
            err_pending_q[si] <= 1'b1;
            err_id_q[si]      <= masters[si].req_id;
            busy_q[si]        <= 1'b1;
          end
        end
        if (err_pending_q[si] && masters[si].rsp_ready) begin
          // rsp_valid is implied 1 when err_pending_q is 1.
          err_pending_q[si] <= 1'b0;
          busy_q[si]        <= 1'b0;
        end
      end

      // Per-slave locking/arbitration and response completion.
      for (si = 0; si < int'(N); si++) begin
        if (inflight_q[si]) begin
          if (slaves[si].rsp_valid && slaves[si].rsp_ready) begin
            inflight_q[si] <= 1'b0;
            busy_q[resp_m_q[si]] <= 1'b0;
          end
        end else begin
          if (lock_q[si]) begin
            if (slaves[si].req_valid && slaves[si].req_ready) begin
              inflight_q[si] <= 1'b1;
              resp_m_q[si]   <= lock_m_q[si];
              busy_q[lock_m_q[si]] <= 1'b1;
              rr_ptr_q[si]   <= lock_m_q[si] + 1'b1;
              lock_q[si]     <= 1'b0;
            end
          end else begin
            logic [M-1:0] req_vec;
            int unsigned winner;

            req_vec = '0;
            for (m = 0; m < int'(M); m++) begin
              if (!busy_q[m] && !err_pending_q[m]) begin
                if (masters[m].req_valid && !dec_err[m] && (dec_idx[m] == logic'(si[N_W-1:0]))) begin
                  req_vec[m] = 1'b1;
                end
              end
            end

            winner = pick_rr(int'(rr_ptr_q[si]), req_vec);
            if (winner < int'(M)) begin
              lock_q[si]   <= 1'b1;
              lock_m_q[si] <= logic'(winner[M_W-1:0]);
            end
          end
        end
      end
    end
  end

endmodule : fabric_arbiter_mxn
