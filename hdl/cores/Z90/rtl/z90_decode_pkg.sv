// Project Carbon - Z90 core (turbo successor, ISA-agnostic infrastructure user)
// z90_decode_pkg: Helpers for decoding Z90 opcode pages.

package z90_decode_pkg;

  function automatic logic [3:0] hi_nibble(input logic [7:0] b);
    return b[7:4];
  endfunction

  function automatic logic [3:0] lo_nibble(input logic [7:0] b);
    return b[3:0];
  endfunction

  function automatic logic signed [15:0] sext8_to_s16(input logic [7:0] b);
    return $signed({{8{b[7]}}, b});
  endfunction

endpackage : z90_decode_pkg
