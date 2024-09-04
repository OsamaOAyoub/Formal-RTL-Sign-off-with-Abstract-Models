`include "sha512_core.v"
`include "sha512_k_constants.v"
`include "sha512_h_constants.v"
`include "sha512_w_mem.v"
`include "global_package.sv"
`include "SHA512_computational.sv"
`include "SHA512_control.sv"
`include "SHA512_operations.sv"
`include "SHA512.sv"
`include "fv_constraints.sv"

//Wrapper definition
module VerificationWrapper (
  input wire clk,
  input wire reset_n,
  input wire zeroize,
  input wire init_cmd,
  input wire next_cmd,
  input wire [1:0] mode,
  input wire [1023:0] block_msg,
  output wire ready,
  output wire [511:0] digest,
  output wire digest_valid
);

//DUT instantiation
sha512_core dut_inst (
  .clk(clk),
  .reset_n(!reset_n),
  .zeroize(zeroize),
  .init_cmd(init_cmd),
  .next_cmd(next_cmd),
  .mode(mode),
  .block_msg(block_msg),
  .ready(ready),
  .digest(digest),
  .digest_valid(digest_valid)
);

//Signals assignments for structs
st_SHA_Args SHA_Input_sig;
assign SHA_Input_sig.init = init_cmd;
assign SHA_Input_sig.next = next_cmd;
assign SHA_Input_sig.zeroize = zeroize;
assign SHA_Input_sig.SHA_Mode = ((mode==0)?224:(mode==1)?256:(mode==2)?384:512);
assign SHA_Input_sig.in = block_msg;

//Generated RTL instantiation
SHA512 SHA512 (
  .rst(reset_n || zeroize),
  .clk(clk),
  .SHA_Input_sig(SHA_Input_sig),
  .SHA_Input_sync(init_cmd || next_cmd),
  .SHA_Input_notify(),
  .out_sig(),
  .out_notify()
);

default clocking default_clk @(posedge clk); endclocking

function bit xnr (input logic [1023:0] sig, input logic [1023:0] sig1);
  return &(~((sig | sig1) & (~sig | ~sig1)));
endfunction

sequence reset_sequence;
  reset_n || zeroize ##1 !(reset_n || zeroize);
endsequence

sequence reset_p_sequence;
  reset_sequence;
endsequence

sequence DONE_to_IDLE_p_sequence;
  (SHA512.SHA512_control_inst.current_state==2);
endsequence

sequence IDLE_to_SHARounds_p_sequence;
  (SHA512.SHA512_control_inst.current_state==0) &&
  SHA512.SHA_Input_sync &&
  SHA512.SHA_Input_sig.init &&
  (SHA512.SHA_Input_sig.SHA_Mode == 'sd224);
endsequence

sequence IDLE_to_SHARounds_1_p_sequence;
  (SHA512.SHA512_control_inst.current_state==0) &&
  SHA512.SHA_Input_sync &&
  SHA512.SHA_Input_sig.init &&
  (SHA512.SHA_Input_sig.SHA_Mode == 'sd256);
endsequence

sequence IDLE_to_SHARounds_2_p_sequence;
  (SHA512.SHA512_control_inst.current_state==0) &&
  SHA512.SHA_Input_sync &&
  SHA512.SHA_Input_sig.init &&
  (SHA512.SHA_Input_sig.SHA_Mode == 'sd512);
endsequence

sequence IDLE_to_SHARounds_3_p_sequence;
  (SHA512.SHA512_control_inst.current_state==0) &&
  SHA512.SHA_Input_sync &&
  SHA512.SHA_Input_sig.init &&
  (SHA512.SHA_Input_sig.SHA_Mode != 'sd224) &&
  (SHA512.SHA_Input_sig.SHA_Mode != 'sd256) &&
  (SHA512.SHA_Input_sig.SHA_Mode != 'sd512);
endsequence

sequence IDLE_to_SHARounds_4_p_sequence;
  (SHA512.SHA512_control_inst.current_state==0) &&
  SHA512.SHA_Input_sync &&
  !SHA512.SHA_Input_sig.init;
endsequence

sequence SHARounds_to_DONE_p_sequence;
  (SHA512.SHA512_control_inst.current_state==1) &&
  (SHA512.SHA512_computational_inst.i >= 'sd16) &&
  (('sd1 + SHA512.SHA512_computational_inst.i) >= 'sd80);
endsequence

sequence SHARounds_to_SHARounds_p_sequence;
  (SHA512.SHA512_control_inst.current_state==1) &&
  (SHA512.SHA512_computational_inst.i < 'sd16);
endsequence

sequence SHARounds_to_SHARounds_1_p_sequence;
  (SHA512.SHA512_control_inst.current_state==1) &&
  (SHA512.SHA512_computational_inst.i >= 'sd16) &&
  (('sd1 + SHA512.SHA512_computational_inst.i) < 'sd80);
endsequence

sequence IDLE_wait_p_sequence;
  (SHA512.SHA512_control_inst.current_state==0) &&
  !SHA512.SHA_Input_sync;
endsequence

reset_a_SHA_Input_notify_ec: assert property (reset_p_SHA_Input_notify_ec);
property reset_p_SHA_Input_notify_ec;
  bit SHA_Input_notify_store; //Store the value of the output from the generated RTL
  reset_p_sequence
  ##0 (1'b1, SHA_Input_notify_store = SHA512.SHA_Input_notify)
  |->
  ##[0:0] SHA_Input_notify_store == ready;
endproperty

reset_a_out_notify_ec: assert property (reset_p_out_notify_ec);
property reset_p_out_notify_ec;
  bit out_notify_store; //Store the value of the output from the generated RTL
  reset_p_sequence
  ##0 (1'b1, out_notify_store = SHA512.out_notify)
  |->
  ##[0:0] out_notify_store == digest_valid;
endproperty

DONE_to_IDLE_a_SHA_Input_notify_ec: assert property (disable iff(reset_n || zeroize) DONE_to_IDLE_p_SHA_Input_notify_ec);
property DONE_to_IDLE_p_SHA_Input_notify_ec;
  bit SHA_Input_notify_store; //Store the value of the output from the generated RTL
  DONE_to_IDLE_p_sequence
  ##1 (1'b1, SHA_Input_notify_store = SHA512.SHA_Input_notify)
  |->
  ##[0:1] SHA_Input_notify_store == ready;
endproperty

DONE_to_IDLE_a_out_sig_ec: assert property (disable iff(reset_n || zeroize) DONE_to_IDLE_p_out_sig_ec);
property DONE_to_IDLE_p_out_sig_ec;
  bit unsigned [511:0] out_sig_store; //Store the value of the output from the generated RTL
  DONE_to_IDLE_p_sequence
  ##1 (1'b1, out_sig_store = SHA512.out_sig)
  ##0 (digest_valid) [->1]
  ##0 (ready) [->1]
  |->
  out_sig_store == digest;
endproperty

DONE_to_IDLE_a_out_notify_ec: assert property (disable iff(reset_n || zeroize) DONE_to_IDLE_p_out_notify_ec);
property DONE_to_IDLE_p_out_notify_ec;
  bit out_notify_store; //Store the value of the output from the generated RTL
  DONE_to_IDLE_p_sequence
  ##1 (1'b1, out_notify_store = SHA512.out_notify)
  |->
  ##[0:1] out_notify_store == digest_valid;
endproperty

//Internal transition assertion, checks hsk signals
IDLE_to_SHARounds_a_ec: assert property (disable iff(reset_n || zeroize) IDLE_to_SHARounds_p_ec);
property IDLE_to_SHARounds_p_ec;
  IDLE_to_SHARounds_p_sequence
  |->
  ##1 (ready == 0) and
  ##1 (digest_valid == 0);
endproperty

//Internal transition assertion, checks hsk signals
IDLE_to_SHARounds_1_a_ec: assert property (disable iff(reset_n || zeroize) IDLE_to_SHARounds_1_p_ec);
property IDLE_to_SHARounds_1_p_ec;
  IDLE_to_SHARounds_1_p_sequence
  |->
  ##1 (ready == 0) and
  ##1 (digest_valid == 0);
endproperty

//Internal transition assertion, checks hsk signals
IDLE_to_SHARounds_2_a_ec: assert property (disable iff(reset_n || zeroize) IDLE_to_SHARounds_2_p_ec);
property IDLE_to_SHARounds_2_p_ec;
  IDLE_to_SHARounds_2_p_sequence
  |->
  ##1 (ready == 0) and
  ##1 (digest_valid == 0);
endproperty

//Internal transition assertion, checks hsk signals
IDLE_to_SHARounds_3_a_ec: assert property (disable iff(reset_n || zeroize) IDLE_to_SHARounds_3_p_ec);
property IDLE_to_SHARounds_3_p_ec;
  IDLE_to_SHARounds_3_p_sequence
  |->
  ##1 (ready == 0) and
  ##1 (digest_valid == 0);
endproperty

//Internal transition assertion, checks hsk signals
IDLE_to_SHARounds_4_a_ec: assert property (disable iff(reset_n || zeroize) IDLE_to_SHARounds_4_p_ec);
property IDLE_to_SHARounds_4_p_ec;
  IDLE_to_SHARounds_4_p_sequence
  |->
  ##1 (ready == 0) and
  ##1 (digest_valid == 0);
endproperty

//Internal transition assertion, checks hsk signals
SHARounds_to_DONE_a_ec: assert property (disable iff(reset_n || zeroize) SHARounds_to_DONE_p_ec);
property SHARounds_to_DONE_p_ec;
  SHARounds_to_DONE_p_sequence
  |->
  ##1 (ready == 0) and
  ##1 (digest_valid == 0);
endproperty

//Internal transition assertion, checks hsk signals
SHARounds_to_SHARounds_a_ec: assert property (disable iff(reset_n || zeroize) SHARounds_to_SHARounds_p_ec);
property SHARounds_to_SHARounds_p_ec;
  SHARounds_to_SHARounds_p_sequence
  |->
  ##1 (ready == 0) and
  ##1 (digest_valid == 0);
endproperty

//Internal transition assertion, checks hsk signals
SHARounds_to_SHARounds_1_a_ec: assert property (disable iff(reset_n || zeroize) SHARounds_to_SHARounds_1_p_ec);
property SHARounds_to_SHARounds_1_p_ec;
  SHARounds_to_SHARounds_1_p_sequence
  |->
  ##1 (ready == 0) and
  ##1 (digest_valid == 0);
endproperty

IDLE_wait_a_SHA_Input_notify_ec: assert property (disable iff(reset_n || zeroize) IDLE_wait_p_SHA_Input_notify_ec);
property IDLE_wait_p_SHA_Input_notify_ec;
  bit SHA_Input_notify_store; //Store the value of the output from the generated RTL
  IDLE_wait_p_sequence
  ##1 (1'b1, SHA_Input_notify_store = SHA512.SHA_Input_notify)
  |->
  ##[0:1] SHA_Input_notify_store == ready;
endproperty

IDLE_wait_a_out_notify_ec: assert property (disable iff(reset_n || zeroize) IDLE_wait_p_out_notify_ec);
property IDLE_wait_p_out_notify_ec;
  bit out_notify_store; //Store the value of the output from the generated RTL
  IDLE_wait_p_sequence
  ##1 (1'b1, out_notify_store = SHA512.out_notify)
  |->
  ##[0:1] out_notify_store == digest_valid;
endproperty


endmodule