// Project Carbon - eZ90 P7 core scaffold
// fe_decode: Decode stub that produces NOP uops (v1 bring-up).

module fe_decode (
    input logic clk,
    input logic rst_n,

    input  logic        inst_valid,
    input  logic [63:0] inst_pc,
    input  logic [31:0] inst_word,
    input  logic        inst_fault,
    output logic        inst_ready,

    output logic             uop_valid,
    output ez90_pkg::ez90_uop_t uop,
    input  logic             uop_ready
);
  import ez90_pkg::*;

  assign inst_ready = uop_ready;
  assign uop_valid  = inst_valid;

  always_comb begin
    uop = '0;
    uop.pc = inst_pc;
    uop.op = 8'(EZ90_UOP_NOP);
    uop.fu = EZ90_FU_INT;
    uop.rd_valid = 1'b0;
    uop.rd = '0;
    uop.rs1 = '0;
    uop.rs2 = '0;
    uop.imm = '0;
    uop.is_load = 1'b0;
    uop.is_store = 1'b0;
    uop.is_branch = 1'b0;
    uop.is_vec = 1'b0;
  end

  wire _unused = clk ^ rst_n ^ inst_word[0] ^ inst_fault;

endmodule : fe_decode

