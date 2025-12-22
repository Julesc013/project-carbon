// Project Carbon - Z480 P7 core scaffold
// scheduler: Select-ready skeleton; routes one uop/cycle to a functional unit.

module scheduler (
    input logic clk,
    input logic rst_n,

    input  logic                      flush,

    input  logic                      rs_valid,
    input  z480_pkg::z480_uop_tagged_t rs_uop,
    output logic                      rs_ready,

    input  logic                      lsq_valid,
    input  z480_pkg::z480_uop_tagged_t lsq_uop,
    output logic                      lsq_ready,

    output logic                      int_valid,
    output z480_pkg::z480_uop_tagged_t int_uop,
    input  logic                      int_ready,

    output logic                      br_valid,
    output z480_pkg::z480_uop_tagged_t br_uop,
    input  logic                      br_ready,

    output logic                      md_valid,
    output z480_pkg::z480_uop_tagged_t md_uop,
    input  logic                      md_ready,

    output logic                      vec_valid,
    output z480_pkg::z480_uop_tagged_t vec_uop,
    input  logic                      vec_ready,

    output logic                      mem_valid,
    output z480_pkg::z480_uop_tagged_t mem_uop,
    input  logic                      mem_ready
);
  import z480_pkg::*;

  always_comb begin
    rs_ready  = 1'b0;
    lsq_ready = 1'b0;

    int_valid = 1'b0; int_uop = '0;
    br_valid  = 1'b0; br_uop  = '0;
    md_valid  = 1'b0; md_uop  = '0;
    vec_valid = 1'b0; vec_uop = '0;
    mem_valid = 1'b0; mem_uop = '0;

    if (!flush) begin
      z480_uop_tagged_t sel;
      logic sel_valid;
      sel = '0;
      sel_valid = 1'b0;

      if (rs_valid) begin
        sel = rs_uop;
        sel_valid = 1'b1;
      end else if (lsq_valid) begin
        sel = lsq_uop;
        sel_valid = 1'b1;
      end

      if (sel_valid) begin
        unique case (sel.uop.uop.fu)
          Z480_FU_BRANCH: begin
            br_valid = 1'b1;
            br_uop   = sel;
            if (br_ready) begin
              if (rs_valid) rs_ready = 1'b1;
              else lsq_ready = 1'b1;
            end
          end
          Z480_FU_MULDIV: begin
            md_valid = 1'b1;
            md_uop   = sel;
            if (md_ready) begin
              if (rs_valid) rs_ready = 1'b1;
              else lsq_ready = 1'b1;
            end
          end
          Z480_FU_VEC: begin
            vec_valid = 1'b1;
            vec_uop   = sel;
            if (vec_ready) begin
              if (rs_valid) rs_ready = 1'b1;
              else lsq_ready = 1'b1;
            end
          end
          Z480_FU_MEM: begin
            mem_valid = 1'b1;
            mem_uop   = sel;
            if (mem_ready) begin
              if (rs_valid) rs_ready = 1'b1;
              else lsq_ready = 1'b1;
            end
          end
          default: begin
            int_valid = 1'b1;
            int_uop   = sel;
            if (int_ready) begin
              if (rs_valid) rs_ready = 1'b1;
              else lsq_ready = 1'b1;
            end
          end
        endcase
      end
    end
  end

  wire _unused = clk ^ rst_n;

endmodule : scheduler
