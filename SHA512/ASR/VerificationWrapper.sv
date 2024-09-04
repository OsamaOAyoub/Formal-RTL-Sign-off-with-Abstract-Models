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

sequence reset_sequence;
  reset_n || zeroize ##1 !reset_n || zeroize;
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

//Smart states refiner properties

//RefinementVector binding
logic [39:0] RefinementVector;
assign RefinementVector[0] = dut_inst.init_cmd;
assign RefinementVector[1] = dut_inst.next_cmd;
assign RefinementVector[3:2] = dut_inst.mode;
assign RefinementVector[4] = dut_inst.ready;
assign RefinementVector[11:5] = dut_inst.round_ctr_reg;
assign RefinementVector[18:12] = dut_inst.round_ctr_new;
assign RefinementVector[19] = dut_inst.round_ctr_we;
assign RefinementVector[20] = dut_inst.round_ctr_inc;
assign RefinementVector[21] = dut_inst.round_ctr_rst;
assign RefinementVector[22] = dut_inst.ready_reg;
assign RefinementVector[23] = dut_inst.ready_new;
assign RefinementVector[24] = dut_inst.ready_we;
assign RefinementVector[25] = dut_inst.digest_valid_reg;
assign RefinementVector[26] = dut_inst.digest_valid_new;
assign RefinementVector[27] = dut_inst.digest_valid_we;
assign RefinementVector[29:28] = dut_inst.sha512_ctrl_reg;
assign RefinementVector[31:30] = dut_inst.sha512_ctrl_new;
assign RefinementVector[32] = dut_inst.digest_valid_we;
assign RefinementVector[33] = dut_inst.digest_init;
assign RefinementVector[34] = dut_inst.digest_update;
assign RefinementVector[35] = dut_inst.state_init;
assign RefinementVector[36] = dut_inst.state_update;
assign RefinementVector[37] = dut_inst.first_block;
assign RefinementVector[38] = dut_inst.w_init;
assign RefinementVector[39] = dut_inst.w_next;


//Bit blasting properties

/**************************************/
/* IDLE state bit-blasting properties */
/**************************************/

//DONE_to_IDLE_p_sequence
for(genvar bitNum = 0; bitNum < 40 ; bitNum++) begin: IDLE__blasting__DONE_to_IDLE_p_sequence_gen
 IDLE__blasting__DONE_to_IDLE_p_sequence_a: assert property (disable iff(reset_n || zeroize)IDLE__blasting__DONE_to_IDLE_p_sequence(bitNum));
 IDLE__blasting__DONE_to_IDLE_p_sequence_NOT_a: assert property (disable iff(reset_n || zeroize)IDLE__blasting__DONE_to_IDLE_p_sequence_NOT(bitNum));
end

property IDLE__blasting__DONE_to_IDLE_p_sequence(bitPos);
 DONE_to_IDLE_p_sequence
|->
 ##1 RefinementVector[bitPos];
endproperty

property IDLE__blasting__DONE_to_IDLE_p_sequence_NOT(bitPos);
 DONE_to_IDLE_p_sequence
|->
 ##1 !RefinementVector[bitPos];
endproperty

//IDLE_wait_p_sequence
for(genvar bitNum = 0; bitNum < 40 ; bitNum++) begin: IDLE__blasting__IDLE_wait_p_sequence_gen
 IDLE__blasting__IDLE_wait_p_sequence_a: assert property (disable iff(reset_n || zeroize)IDLE__blasting__IDLE_wait_p_sequence(bitNum));
 IDLE__blasting__IDLE_wait_p_sequence_NOT_a: assert property (disable iff(reset_n || zeroize)IDLE__blasting__IDLE_wait_p_sequence_NOT(bitNum));
end

property IDLE__blasting__IDLE_wait_p_sequence(bitPos);
 IDLE_wait_p_sequence
|->
 ##1 RefinementVector[bitPos];
endproperty

property IDLE__blasting__IDLE_wait_p_sequence_NOT(bitPos);
 IDLE_wait_p_sequence
|->
 ##1 !RefinementVector[bitPos];
endproperty

//reset_p_sequence
for(genvar bitNum = 0; bitNum < 40 ; bitNum++) begin: IDLE__blasting__reset_p_sequence_gen
 IDLE__blasting__reset_p_sequence_a: assert property (IDLE__blasting__reset_p_sequence(bitNum));
 IDLE__blasting__reset_p_sequence_NOT_a: assert property (IDLE__blasting__reset_p_sequence_NOT(bitNum));
end

property IDLE__blasting__reset_p_sequence(bitPos);
 reset_p_sequence
|->
 RefinementVector[bitPos];
endproperty

property IDLE__blasting__reset_p_sequence_NOT(bitPos);
 reset_p_sequence
|->
 !RefinementVector[bitPos];
endproperty


/*******************************************/
/* SHARounds state bit-blasting properties */
/*******************************************/

//IDLE_to_SHARounds_p_sequence
for(genvar bitNum = 0; bitNum < 40 ; bitNum++) begin: SHARounds__blasting__IDLE_to_SHARounds_p_sequence_gen
 SHARounds__blasting__IDLE_to_SHARounds_p_sequence_a: assert property (disable iff(reset_n || zeroize)SHARounds__blasting__IDLE_to_SHARounds_p_sequence(bitNum));
 SHARounds__blasting__IDLE_to_SHARounds_p_sequence_NOT_a: assert property (disable iff(reset_n || zeroize)SHARounds__blasting__IDLE_to_SHARounds_p_sequence_NOT(bitNum));
end

property SHARounds__blasting__IDLE_to_SHARounds_p_sequence(bitPos);
 IDLE_to_SHARounds_p_sequence
|->
 ##1 RefinementVector[bitPos];
endproperty

property SHARounds__blasting__IDLE_to_SHARounds_p_sequence_NOT(bitPos);
 IDLE_to_SHARounds_p_sequence
|->
 ##1 !RefinementVector[bitPos];
endproperty

//IDLE_to_SHARounds_1_p_sequence
for(genvar bitNum = 0; bitNum < 40 ; bitNum++) begin: SHARounds__blasting__IDLE_to_SHARounds_1_p_sequence_gen
 SHARounds__blasting__IDLE_to_SHARounds_1_p_sequence_a: assert property (disable iff(reset_n || zeroize)SHARounds__blasting__IDLE_to_SHARounds_1_p_sequence(bitNum));
 SHARounds__blasting__IDLE_to_SHARounds_1_p_sequence_NOT_a: assert property (disable iff(reset_n || zeroize)SHARounds__blasting__IDLE_to_SHARounds_1_p_sequence_NOT(bitNum));
end

property SHARounds__blasting__IDLE_to_SHARounds_1_p_sequence(bitPos);
 IDLE_to_SHARounds_1_p_sequence
|->
 ##1 RefinementVector[bitPos];
endproperty

property SHARounds__blasting__IDLE_to_SHARounds_1_p_sequence_NOT(bitPos);
 IDLE_to_SHARounds_1_p_sequence
|->
 ##1 !RefinementVector[bitPos];
endproperty

//IDLE_to_SHARounds_2_p_sequence
for(genvar bitNum = 0; bitNum < 40 ; bitNum++) begin: SHARounds__blasting__IDLE_to_SHARounds_2_p_sequence_gen
 SHARounds__blasting__IDLE_to_SHARounds_2_p_sequence_a: assert property (disable iff(reset_n || zeroize)SHARounds__blasting__IDLE_to_SHARounds_2_p_sequence(bitNum));
 SHARounds__blasting__IDLE_to_SHARounds_2_p_sequence_NOT_a: assert property (disable iff(reset_n || zeroize)SHARounds__blasting__IDLE_to_SHARounds_2_p_sequence_NOT(bitNum));
end

property SHARounds__blasting__IDLE_to_SHARounds_2_p_sequence(bitPos);
 IDLE_to_SHARounds_2_p_sequence
|->
 ##1 RefinementVector[bitPos];
endproperty

property SHARounds__blasting__IDLE_to_SHARounds_2_p_sequence_NOT(bitPos);
 IDLE_to_SHARounds_2_p_sequence
|->
 ##1 !RefinementVector[bitPos];
endproperty

//IDLE_to_SHARounds_3_p_sequence
for(genvar bitNum = 0; bitNum < 40 ; bitNum++) begin: SHARounds__blasting__IDLE_to_SHARounds_3_p_sequence_gen
 SHARounds__blasting__IDLE_to_SHARounds_3_p_sequence_a: assert property (disable iff(reset_n || zeroize)SHARounds__blasting__IDLE_to_SHARounds_3_p_sequence(bitNum));
 SHARounds__blasting__IDLE_to_SHARounds_3_p_sequence_NOT_a: assert property (disable iff(reset_n || zeroize)SHARounds__blasting__IDLE_to_SHARounds_3_p_sequence_NOT(bitNum));
end

property SHARounds__blasting__IDLE_to_SHARounds_3_p_sequence(bitPos);
 IDLE_to_SHARounds_3_p_sequence
|->
 ##1 RefinementVector[bitPos];
endproperty

property SHARounds__blasting__IDLE_to_SHARounds_3_p_sequence_NOT(bitPos);
 IDLE_to_SHARounds_3_p_sequence
|->
 ##1 !RefinementVector[bitPos];
endproperty

//IDLE_to_SHARounds_4_p_sequence
for(genvar bitNum = 0; bitNum < 40 ; bitNum++) begin: SHARounds__blasting__IDLE_to_SHARounds_4_p_sequence_gen
 SHARounds__blasting__IDLE_to_SHARounds_4_p_sequence_a: assert property (disable iff(reset_n || zeroize)SHARounds__blasting__IDLE_to_SHARounds_4_p_sequence(bitNum));
 SHARounds__blasting__IDLE_to_SHARounds_4_p_sequence_NOT_a: assert property (disable iff(reset_n || zeroize)SHARounds__blasting__IDLE_to_SHARounds_4_p_sequence_NOT(bitNum));
end

property SHARounds__blasting__IDLE_to_SHARounds_4_p_sequence(bitPos);
 IDLE_to_SHARounds_4_p_sequence
|->
 ##1 RefinementVector[bitPos];
endproperty

property SHARounds__blasting__IDLE_to_SHARounds_4_p_sequence_NOT(bitPos);
 IDLE_to_SHARounds_4_p_sequence
|->
 ##1 !RefinementVector[bitPos];
endproperty

//SHARounds_to_SHARounds_p_sequence
for(genvar bitNum = 0; bitNum < 40 ; bitNum++) begin: SHARounds__blasting__SHARounds_to_SHARounds_p_sequence_gen
 SHARounds__blasting__SHARounds_to_SHARounds_p_sequence_a: assert property (disable iff(reset_n || zeroize)SHARounds__blasting__SHARounds_to_SHARounds_p_sequence(bitNum));
 SHARounds__blasting__SHARounds_to_SHARounds_p_sequence_NOT_a: assert property (disable iff(reset_n || zeroize)SHARounds__blasting__SHARounds_to_SHARounds_p_sequence_NOT(bitNum));
end

property SHARounds__blasting__SHARounds_to_SHARounds_p_sequence(bitPos);
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 RefinementVector[bitPos];
endproperty

property SHARounds__blasting__SHARounds_to_SHARounds_p_sequence_NOT(bitPos);
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 !RefinementVector[bitPos];
endproperty

//SHARounds_to_SHARounds_1_p_sequence
for(genvar bitNum = 0; bitNum < 40 ; bitNum++) begin: SHARounds__blasting__SHARounds_to_SHARounds_1_p_sequence_gen
 SHARounds__blasting__SHARounds_to_SHARounds_1_p_sequence_a: assert property (disable iff(reset_n || zeroize)SHARounds__blasting__SHARounds_to_SHARounds_1_p_sequence(bitNum));
 SHARounds__blasting__SHARounds_to_SHARounds_1_p_sequence_NOT_a: assert property (disable iff(reset_n || zeroize)SHARounds__blasting__SHARounds_to_SHARounds_1_p_sequence_NOT(bitNum));
end

property SHARounds__blasting__SHARounds_to_SHARounds_1_p_sequence(bitPos);
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 RefinementVector[bitPos];
endproperty

property SHARounds__blasting__SHARounds_to_SHARounds_1_p_sequence_NOT(bitPos);
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 !RefinementVector[bitPos];
endproperty


/**************************************/
/* DONE state bit-blasting properties */
/**************************************/

//SHARounds_to_DONE_p_sequence
for(genvar bitNum = 0; bitNum < 40 ; bitNum++) begin: DONE__blasting__SHARounds_to_DONE_p_sequence_gen
 DONE__blasting__SHARounds_to_DONE_p_sequence_a: assert property (disable iff(reset_n || zeroize)DONE__blasting__SHARounds_to_DONE_p_sequence(bitNum));
 DONE__blasting__SHARounds_to_DONE_p_sequence_NOT_a: assert property (disable iff(reset_n || zeroize)DONE__blasting__SHARounds_to_DONE_p_sequence_NOT(bitNum));
end

property DONE__blasting__SHARounds_to_DONE_p_sequence(bitPos);
 SHARounds_to_DONE_p_sequence
|->
 ##1 RefinementVector[bitPos];
endproperty

property DONE__blasting__SHARounds_to_DONE_p_sequence_NOT(bitPos);
 SHARounds_to_DONE_p_sequence
|->
 ##1 !RefinementVector[bitPos];
endproperty


//Bit pairing properties

/*************************************/
/* IDLE state bit-pairing properties */
/*************************************/

//DONE_to_IDLE_p_sequence
//pair: {0,1}
IDLE__pairing__DONE_to_IDLE_p_sequence__0__0_1_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__0__0_1);
property IDLE__pairing__DONE_to_IDLE_p_sequence__0__0_1;
 DONE_to_IDLE_p_sequence
|->
 ##1 !RefinementVector[0]
 && !RefinementVector[1];
endproperty

IDLE__pairing__DONE_to_IDLE_p_sequence__1__0_1_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__1__0_1);
property IDLE__pairing__DONE_to_IDLE_p_sequence__1__0_1;
 DONE_to_IDLE_p_sequence
|->
 ##1 RefinementVector[0]
 && !RefinementVector[1];
endproperty

IDLE__pairing__DONE_to_IDLE_p_sequence__2__0_1_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__2__0_1);
property IDLE__pairing__DONE_to_IDLE_p_sequence__2__0_1;
 DONE_to_IDLE_p_sequence
|->
 ##1 !RefinementVector[0]
 && RefinementVector[1];
endproperty

IDLE__pairing__DONE_to_IDLE_p_sequence__3__0_1_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__3__0_1);
property IDLE__pairing__DONE_to_IDLE_p_sequence__3__0_1;
 DONE_to_IDLE_p_sequence
|->
 ##1 RefinementVector[0]
 && RefinementVector[1];
endproperty

//DONE_to_IDLE_p_sequence
//pair: {1,2}
IDLE__pairing__DONE_to_IDLE_p_sequence__0__1_2_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__0__1_2);
property IDLE__pairing__DONE_to_IDLE_p_sequence__0__1_2;
 DONE_to_IDLE_p_sequence
|->
 ##1 !RefinementVector[1]
 && !RefinementVector[2];
endproperty

IDLE__pairing__DONE_to_IDLE_p_sequence__1__1_2_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__1__1_2);
property IDLE__pairing__DONE_to_IDLE_p_sequence__1__1_2;
 DONE_to_IDLE_p_sequence
|->
 ##1 RefinementVector[1]
 && !RefinementVector[2];
endproperty

IDLE__pairing__DONE_to_IDLE_p_sequence__2__1_2_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__2__1_2);
property IDLE__pairing__DONE_to_IDLE_p_sequence__2__1_2;
 DONE_to_IDLE_p_sequence
|->
 ##1 !RefinementVector[1]
 && RefinementVector[2];
endproperty

IDLE__pairing__DONE_to_IDLE_p_sequence__3__1_2_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__3__1_2);
property IDLE__pairing__DONE_to_IDLE_p_sequence__3__1_2;
 DONE_to_IDLE_p_sequence
|->
 ##1 RefinementVector[1]
 && RefinementVector[2];
endproperty

//DONE_to_IDLE_p_sequence
//pair: {2,3}
IDLE__pairing__DONE_to_IDLE_p_sequence__0__2_3_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__0__2_3);
property IDLE__pairing__DONE_to_IDLE_p_sequence__0__2_3;
 DONE_to_IDLE_p_sequence
|->
 ##1 !RefinementVector[2]
 && !RefinementVector[3];
endproperty

IDLE__pairing__DONE_to_IDLE_p_sequence__1__2_3_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__1__2_3);
property IDLE__pairing__DONE_to_IDLE_p_sequence__1__2_3;
 DONE_to_IDLE_p_sequence
|->
 ##1 RefinementVector[2]
 && !RefinementVector[3];
endproperty

IDLE__pairing__DONE_to_IDLE_p_sequence__2__2_3_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__2__2_3);
property IDLE__pairing__DONE_to_IDLE_p_sequence__2__2_3;
 DONE_to_IDLE_p_sequence
|->
 ##1 !RefinementVector[2]
 && RefinementVector[3];
endproperty

IDLE__pairing__DONE_to_IDLE_p_sequence__3__2_3_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__3__2_3);
property IDLE__pairing__DONE_to_IDLE_p_sequence__3__2_3;
 DONE_to_IDLE_p_sequence
|->
 ##1 RefinementVector[2]
 && RefinementVector[3];
endproperty

//DONE_to_IDLE_p_sequence
//pair: {3,19}
IDLE__pairing__DONE_to_IDLE_p_sequence__0__3_19_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__0__3_19);
property IDLE__pairing__DONE_to_IDLE_p_sequence__0__3_19;
 DONE_to_IDLE_p_sequence
|->
 ##1 !RefinementVector[3]
 && !RefinementVector[19];
endproperty

IDLE__pairing__DONE_to_IDLE_p_sequence__1__3_19_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__1__3_19);
property IDLE__pairing__DONE_to_IDLE_p_sequence__1__3_19;
 DONE_to_IDLE_p_sequence
|->
 ##1 RefinementVector[3]
 && !RefinementVector[19];
endproperty

IDLE__pairing__DONE_to_IDLE_p_sequence__2__3_19_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__2__3_19);
property IDLE__pairing__DONE_to_IDLE_p_sequence__2__3_19;
 DONE_to_IDLE_p_sequence
|->
 ##1 !RefinementVector[3]
 && RefinementVector[19];
endproperty

IDLE__pairing__DONE_to_IDLE_p_sequence__3__3_19_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__3__3_19);
property IDLE__pairing__DONE_to_IDLE_p_sequence__3__3_19;
 DONE_to_IDLE_p_sequence
|->
 ##1 RefinementVector[3]
 && RefinementVector[19];
endproperty

//DONE_to_IDLE_p_sequence
//pair: {19,21}
IDLE__pairing__DONE_to_IDLE_p_sequence__0__19_21_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__0__19_21);
property IDLE__pairing__DONE_to_IDLE_p_sequence__0__19_21;
 DONE_to_IDLE_p_sequence
|->
 ##1 !RefinementVector[19]
 && !RefinementVector[21];
endproperty

IDLE__pairing__DONE_to_IDLE_p_sequence__1__19_21_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__1__19_21);
property IDLE__pairing__DONE_to_IDLE_p_sequence__1__19_21;
 DONE_to_IDLE_p_sequence
|->
 ##1 RefinementVector[19]
 && !RefinementVector[21];
endproperty

IDLE__pairing__DONE_to_IDLE_p_sequence__2__19_21_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__2__19_21);
property IDLE__pairing__DONE_to_IDLE_p_sequence__2__19_21;
 DONE_to_IDLE_p_sequence
|->
 ##1 !RefinementVector[19]
 && RefinementVector[21];
endproperty

IDLE__pairing__DONE_to_IDLE_p_sequence__3__19_21_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__3__19_21);
property IDLE__pairing__DONE_to_IDLE_p_sequence__3__19_21;
 DONE_to_IDLE_p_sequence
|->
 ##1 RefinementVector[19]
 && RefinementVector[21];
endproperty

//DONE_to_IDLE_p_sequence
//pair: {21,24}
IDLE__pairing__DONE_to_IDLE_p_sequence__0__21_24_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__0__21_24);
property IDLE__pairing__DONE_to_IDLE_p_sequence__0__21_24;
 DONE_to_IDLE_p_sequence
|->
 ##1 !RefinementVector[21]
 && !RefinementVector[24];
endproperty

IDLE__pairing__DONE_to_IDLE_p_sequence__1__21_24_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__1__21_24);
property IDLE__pairing__DONE_to_IDLE_p_sequence__1__21_24;
 DONE_to_IDLE_p_sequence
|->
 ##1 RefinementVector[21]
 && !RefinementVector[24];
endproperty

IDLE__pairing__DONE_to_IDLE_p_sequence__2__21_24_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__2__21_24);
property IDLE__pairing__DONE_to_IDLE_p_sequence__2__21_24;
 DONE_to_IDLE_p_sequence
|->
 ##1 !RefinementVector[21]
 && RefinementVector[24];
endproperty

IDLE__pairing__DONE_to_IDLE_p_sequence__3__21_24_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__3__21_24);
property IDLE__pairing__DONE_to_IDLE_p_sequence__3__21_24;
 DONE_to_IDLE_p_sequence
|->
 ##1 RefinementVector[21]
 && RefinementVector[24];
endproperty

//DONE_to_IDLE_p_sequence
//pair: {24,27}
IDLE__pairing__DONE_to_IDLE_p_sequence__0__24_27_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__0__24_27);
property IDLE__pairing__DONE_to_IDLE_p_sequence__0__24_27;
 DONE_to_IDLE_p_sequence
|->
 ##1 !RefinementVector[24]
 && !RefinementVector[27];
endproperty

IDLE__pairing__DONE_to_IDLE_p_sequence__1__24_27_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__1__24_27);
property IDLE__pairing__DONE_to_IDLE_p_sequence__1__24_27;
 DONE_to_IDLE_p_sequence
|->
 ##1 RefinementVector[24]
 && !RefinementVector[27];
endproperty

IDLE__pairing__DONE_to_IDLE_p_sequence__2__24_27_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__2__24_27);
property IDLE__pairing__DONE_to_IDLE_p_sequence__2__24_27;
 DONE_to_IDLE_p_sequence
|->
 ##1 !RefinementVector[24]
 && RefinementVector[27];
endproperty

IDLE__pairing__DONE_to_IDLE_p_sequence__3__24_27_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__3__24_27);
property IDLE__pairing__DONE_to_IDLE_p_sequence__3__24_27;
 DONE_to_IDLE_p_sequence
|->
 ##1 RefinementVector[24]
 && RefinementVector[27];
endproperty

//DONE_to_IDLE_p_sequence
//pair: {27,30}
IDLE__pairing__DONE_to_IDLE_p_sequence__0__27_30_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__0__27_30);
property IDLE__pairing__DONE_to_IDLE_p_sequence__0__27_30;
 DONE_to_IDLE_p_sequence
|->
 ##1 !RefinementVector[27]
 && !RefinementVector[30];
endproperty

IDLE__pairing__DONE_to_IDLE_p_sequence__1__27_30_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__1__27_30);
property IDLE__pairing__DONE_to_IDLE_p_sequence__1__27_30;
 DONE_to_IDLE_p_sequence
|->
 ##1 RefinementVector[27]
 && !RefinementVector[30];
endproperty

IDLE__pairing__DONE_to_IDLE_p_sequence__2__27_30_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__2__27_30);
property IDLE__pairing__DONE_to_IDLE_p_sequence__2__27_30;
 DONE_to_IDLE_p_sequence
|->
 ##1 !RefinementVector[27]
 && RefinementVector[30];
endproperty

IDLE__pairing__DONE_to_IDLE_p_sequence__3__27_30_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__3__27_30);
property IDLE__pairing__DONE_to_IDLE_p_sequence__3__27_30;
 DONE_to_IDLE_p_sequence
|->
 ##1 RefinementVector[27]
 && RefinementVector[30];
endproperty

//DONE_to_IDLE_p_sequence
//pair: {30,32}
IDLE__pairing__DONE_to_IDLE_p_sequence__0__30_32_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__0__30_32);
property IDLE__pairing__DONE_to_IDLE_p_sequence__0__30_32;
 DONE_to_IDLE_p_sequence
|->
 ##1 !RefinementVector[30]
 && !RefinementVector[32];
endproperty

IDLE__pairing__DONE_to_IDLE_p_sequence__1__30_32_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__1__30_32);
property IDLE__pairing__DONE_to_IDLE_p_sequence__1__30_32;
 DONE_to_IDLE_p_sequence
|->
 ##1 RefinementVector[30]
 && !RefinementVector[32];
endproperty

IDLE__pairing__DONE_to_IDLE_p_sequence__2__30_32_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__2__30_32);
property IDLE__pairing__DONE_to_IDLE_p_sequence__2__30_32;
 DONE_to_IDLE_p_sequence
|->
 ##1 !RefinementVector[30]
 && RefinementVector[32];
endproperty

IDLE__pairing__DONE_to_IDLE_p_sequence__3__30_32_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__3__30_32);
property IDLE__pairing__DONE_to_IDLE_p_sequence__3__30_32;
 DONE_to_IDLE_p_sequence
|->
 ##1 RefinementVector[30]
 && RefinementVector[32];
endproperty

//DONE_to_IDLE_p_sequence
//pair: {32,33}
IDLE__pairing__DONE_to_IDLE_p_sequence__0__32_33_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__0__32_33);
property IDLE__pairing__DONE_to_IDLE_p_sequence__0__32_33;
 DONE_to_IDLE_p_sequence
|->
 ##1 !RefinementVector[32]
 && !RefinementVector[33];
endproperty

IDLE__pairing__DONE_to_IDLE_p_sequence__1__32_33_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__1__32_33);
property IDLE__pairing__DONE_to_IDLE_p_sequence__1__32_33;
 DONE_to_IDLE_p_sequence
|->
 ##1 RefinementVector[32]
 && !RefinementVector[33];
endproperty

IDLE__pairing__DONE_to_IDLE_p_sequence__2__32_33_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__2__32_33);
property IDLE__pairing__DONE_to_IDLE_p_sequence__2__32_33;
 DONE_to_IDLE_p_sequence
|->
 ##1 !RefinementVector[32]
 && RefinementVector[33];
endproperty

IDLE__pairing__DONE_to_IDLE_p_sequence__3__32_33_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__3__32_33);
property IDLE__pairing__DONE_to_IDLE_p_sequence__3__32_33;
 DONE_to_IDLE_p_sequence
|->
 ##1 RefinementVector[32]
 && RefinementVector[33];
endproperty

//DONE_to_IDLE_p_sequence
//pair: {33,35}
IDLE__pairing__DONE_to_IDLE_p_sequence__0__33_35_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__0__33_35);
property IDLE__pairing__DONE_to_IDLE_p_sequence__0__33_35;
 DONE_to_IDLE_p_sequence
|->
 ##1 !RefinementVector[33]
 && !RefinementVector[35];
endproperty

IDLE__pairing__DONE_to_IDLE_p_sequence__1__33_35_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__1__33_35);
property IDLE__pairing__DONE_to_IDLE_p_sequence__1__33_35;
 DONE_to_IDLE_p_sequence
|->
 ##1 RefinementVector[33]
 && !RefinementVector[35];
endproperty

IDLE__pairing__DONE_to_IDLE_p_sequence__2__33_35_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__2__33_35);
property IDLE__pairing__DONE_to_IDLE_p_sequence__2__33_35;
 DONE_to_IDLE_p_sequence
|->
 ##1 !RefinementVector[33]
 && RefinementVector[35];
endproperty

IDLE__pairing__DONE_to_IDLE_p_sequence__3__33_35_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__3__33_35);
property IDLE__pairing__DONE_to_IDLE_p_sequence__3__33_35;
 DONE_to_IDLE_p_sequence
|->
 ##1 RefinementVector[33]
 && RefinementVector[35];
endproperty

//DONE_to_IDLE_p_sequence
//pair: {35,37}
IDLE__pairing__DONE_to_IDLE_p_sequence__0__35_37_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__0__35_37);
property IDLE__pairing__DONE_to_IDLE_p_sequence__0__35_37;
 DONE_to_IDLE_p_sequence
|->
 ##1 !RefinementVector[35]
 && !RefinementVector[37];
endproperty

IDLE__pairing__DONE_to_IDLE_p_sequence__1__35_37_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__1__35_37);
property IDLE__pairing__DONE_to_IDLE_p_sequence__1__35_37;
 DONE_to_IDLE_p_sequence
|->
 ##1 RefinementVector[35]
 && !RefinementVector[37];
endproperty

IDLE__pairing__DONE_to_IDLE_p_sequence__2__35_37_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__2__35_37);
property IDLE__pairing__DONE_to_IDLE_p_sequence__2__35_37;
 DONE_to_IDLE_p_sequence
|->
 ##1 !RefinementVector[35]
 && RefinementVector[37];
endproperty

IDLE__pairing__DONE_to_IDLE_p_sequence__3__35_37_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__3__35_37);
property IDLE__pairing__DONE_to_IDLE_p_sequence__3__35_37;
 DONE_to_IDLE_p_sequence
|->
 ##1 RefinementVector[35]
 && RefinementVector[37];
endproperty

//DONE_to_IDLE_p_sequence
//pair: {37,38}
IDLE__pairing__DONE_to_IDLE_p_sequence__0__37_38_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__0__37_38);
property IDLE__pairing__DONE_to_IDLE_p_sequence__0__37_38;
 DONE_to_IDLE_p_sequence
|->
 ##1 !RefinementVector[37]
 && !RefinementVector[38];
endproperty

IDLE__pairing__DONE_to_IDLE_p_sequence__1__37_38_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__1__37_38);
property IDLE__pairing__DONE_to_IDLE_p_sequence__1__37_38;
 DONE_to_IDLE_p_sequence
|->
 ##1 RefinementVector[37]
 && !RefinementVector[38];
endproperty

IDLE__pairing__DONE_to_IDLE_p_sequence__2__37_38_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__2__37_38);
property IDLE__pairing__DONE_to_IDLE_p_sequence__2__37_38;
 DONE_to_IDLE_p_sequence
|->
 ##1 !RefinementVector[37]
 && RefinementVector[38];
endproperty

IDLE__pairing__DONE_to_IDLE_p_sequence__3__37_38_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__DONE_to_IDLE_p_sequence__3__37_38);
property IDLE__pairing__DONE_to_IDLE_p_sequence__3__37_38;
 DONE_to_IDLE_p_sequence
|->
 ##1 RefinementVector[37]
 && RefinementVector[38];
endproperty


//IDLE_wait_p_sequence
//pair: {0,1}
IDLE__pairing__IDLE_wait_p_sequence__0__0_1_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__0__0_1);
property IDLE__pairing__IDLE_wait_p_sequence__0__0_1;
 IDLE_wait_p_sequence
|->
 ##1 !RefinementVector[0]
 && !RefinementVector[1];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__1__0_1_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__1__0_1);
property IDLE__pairing__IDLE_wait_p_sequence__1__0_1;
 IDLE_wait_p_sequence
|->
 ##1 RefinementVector[0]
 && !RefinementVector[1];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__2__0_1_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__2__0_1);
property IDLE__pairing__IDLE_wait_p_sequence__2__0_1;
 IDLE_wait_p_sequence
|->
 ##1 !RefinementVector[0]
 && RefinementVector[1];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__3__0_1_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__3__0_1);
property IDLE__pairing__IDLE_wait_p_sequence__3__0_1;
 IDLE_wait_p_sequence
|->
 ##1 RefinementVector[0]
 && RefinementVector[1];
endproperty

//IDLE_wait_p_sequence
//pair: {1,2}
IDLE__pairing__IDLE_wait_p_sequence__0__1_2_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__0__1_2);
property IDLE__pairing__IDLE_wait_p_sequence__0__1_2;
 IDLE_wait_p_sequence
|->
 ##1 !RefinementVector[1]
 && !RefinementVector[2];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__1__1_2_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__1__1_2);
property IDLE__pairing__IDLE_wait_p_sequence__1__1_2;
 IDLE_wait_p_sequence
|->
 ##1 RefinementVector[1]
 && !RefinementVector[2];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__2__1_2_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__2__1_2);
property IDLE__pairing__IDLE_wait_p_sequence__2__1_2;
 IDLE_wait_p_sequence
|->
 ##1 !RefinementVector[1]
 && RefinementVector[2];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__3__1_2_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__3__1_2);
property IDLE__pairing__IDLE_wait_p_sequence__3__1_2;
 IDLE_wait_p_sequence
|->
 ##1 RefinementVector[1]
 && RefinementVector[2];
endproperty

//IDLE_wait_p_sequence
//pair: {2,3}
IDLE__pairing__IDLE_wait_p_sequence__0__2_3_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__0__2_3);
property IDLE__pairing__IDLE_wait_p_sequence__0__2_3;
 IDLE_wait_p_sequence
|->
 ##1 !RefinementVector[2]
 && !RefinementVector[3];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__1__2_3_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__1__2_3);
property IDLE__pairing__IDLE_wait_p_sequence__1__2_3;
 IDLE_wait_p_sequence
|->
 ##1 RefinementVector[2]
 && !RefinementVector[3];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__2__2_3_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__2__2_3);
property IDLE__pairing__IDLE_wait_p_sequence__2__2_3;
 IDLE_wait_p_sequence
|->
 ##1 !RefinementVector[2]
 && RefinementVector[3];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__3__2_3_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__3__2_3);
property IDLE__pairing__IDLE_wait_p_sequence__3__2_3;
 IDLE_wait_p_sequence
|->
 ##1 RefinementVector[2]
 && RefinementVector[3];
endproperty

//IDLE_wait_p_sequence
//pair: {3,9}
IDLE__pairing__IDLE_wait_p_sequence__0__3_9_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__0__3_9);
property IDLE__pairing__IDLE_wait_p_sequence__0__3_9;
 IDLE_wait_p_sequence
|->
 ##1 !RefinementVector[3]
 && !RefinementVector[9];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__1__3_9_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__1__3_9);
property IDLE__pairing__IDLE_wait_p_sequence__1__3_9;
 IDLE_wait_p_sequence
|->
 ##1 RefinementVector[3]
 && !RefinementVector[9];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__2__3_9_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__2__3_9);
property IDLE__pairing__IDLE_wait_p_sequence__2__3_9;
 IDLE_wait_p_sequence
|->
 ##1 !RefinementVector[3]
 && RefinementVector[9];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__3__3_9_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__3__3_9);
property IDLE__pairing__IDLE_wait_p_sequence__3__3_9;
 IDLE_wait_p_sequence
|->
 ##1 RefinementVector[3]
 && RefinementVector[9];
endproperty

//IDLE_wait_p_sequence
//pair: {9,11}
IDLE__pairing__IDLE_wait_p_sequence__0__9_11_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__0__9_11);
property IDLE__pairing__IDLE_wait_p_sequence__0__9_11;
 IDLE_wait_p_sequence
|->
 ##1 !RefinementVector[9]
 && !RefinementVector[11];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__1__9_11_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__1__9_11);
property IDLE__pairing__IDLE_wait_p_sequence__1__9_11;
 IDLE_wait_p_sequence
|->
 ##1 RefinementVector[9]
 && !RefinementVector[11];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__2__9_11_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__2__9_11);
property IDLE__pairing__IDLE_wait_p_sequence__2__9_11;
 IDLE_wait_p_sequence
|->
 ##1 !RefinementVector[9]
 && RefinementVector[11];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__3__9_11_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__3__9_11);
property IDLE__pairing__IDLE_wait_p_sequence__3__9_11;
 IDLE_wait_p_sequence
|->
 ##1 RefinementVector[9]
 && RefinementVector[11];
endproperty

//IDLE_wait_p_sequence
//pair: {11,19}
IDLE__pairing__IDLE_wait_p_sequence__0__11_19_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__0__11_19);
property IDLE__pairing__IDLE_wait_p_sequence__0__11_19;
 IDLE_wait_p_sequence
|->
 ##1 !RefinementVector[11]
 && !RefinementVector[19];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__1__11_19_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__1__11_19);
property IDLE__pairing__IDLE_wait_p_sequence__1__11_19;
 IDLE_wait_p_sequence
|->
 ##1 RefinementVector[11]
 && !RefinementVector[19];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__2__11_19_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__2__11_19);
property IDLE__pairing__IDLE_wait_p_sequence__2__11_19;
 IDLE_wait_p_sequence
|->
 ##1 !RefinementVector[11]
 && RefinementVector[19];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__3__11_19_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__3__11_19);
property IDLE__pairing__IDLE_wait_p_sequence__3__11_19;
 IDLE_wait_p_sequence
|->
 ##1 RefinementVector[11]
 && RefinementVector[19];
endproperty

//IDLE_wait_p_sequence
//pair: {19,21}
IDLE__pairing__IDLE_wait_p_sequence__0__19_21_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__0__19_21);
property IDLE__pairing__IDLE_wait_p_sequence__0__19_21;
 IDLE_wait_p_sequence
|->
 ##1 !RefinementVector[19]
 && !RefinementVector[21];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__1__19_21_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__1__19_21);
property IDLE__pairing__IDLE_wait_p_sequence__1__19_21;
 IDLE_wait_p_sequence
|->
 ##1 RefinementVector[19]
 && !RefinementVector[21];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__2__19_21_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__2__19_21);
property IDLE__pairing__IDLE_wait_p_sequence__2__19_21;
 IDLE_wait_p_sequence
|->
 ##1 !RefinementVector[19]
 && RefinementVector[21];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__3__19_21_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__3__19_21);
property IDLE__pairing__IDLE_wait_p_sequence__3__19_21;
 IDLE_wait_p_sequence
|->
 ##1 RefinementVector[19]
 && RefinementVector[21];
endproperty

//IDLE_wait_p_sequence
//pair: {21,24}
IDLE__pairing__IDLE_wait_p_sequence__0__21_24_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__0__21_24);
property IDLE__pairing__IDLE_wait_p_sequence__0__21_24;
 IDLE_wait_p_sequence
|->
 ##1 !RefinementVector[21]
 && !RefinementVector[24];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__1__21_24_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__1__21_24);
property IDLE__pairing__IDLE_wait_p_sequence__1__21_24;
 IDLE_wait_p_sequence
|->
 ##1 RefinementVector[21]
 && !RefinementVector[24];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__2__21_24_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__2__21_24);
property IDLE__pairing__IDLE_wait_p_sequence__2__21_24;
 IDLE_wait_p_sequence
|->
 ##1 !RefinementVector[21]
 && RefinementVector[24];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__3__21_24_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__3__21_24);
property IDLE__pairing__IDLE_wait_p_sequence__3__21_24;
 IDLE_wait_p_sequence
|->
 ##1 RefinementVector[21]
 && RefinementVector[24];
endproperty

//IDLE_wait_p_sequence
//pair: {24,25}
IDLE__pairing__IDLE_wait_p_sequence__0__24_25_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__0__24_25);
property IDLE__pairing__IDLE_wait_p_sequence__0__24_25;
 IDLE_wait_p_sequence
|->
 ##1 !RefinementVector[24]
 && !RefinementVector[25];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__1__24_25_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__1__24_25);
property IDLE__pairing__IDLE_wait_p_sequence__1__24_25;
 IDLE_wait_p_sequence
|->
 ##1 RefinementVector[24]
 && !RefinementVector[25];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__2__24_25_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__2__24_25);
property IDLE__pairing__IDLE_wait_p_sequence__2__24_25;
 IDLE_wait_p_sequence
|->
 ##1 !RefinementVector[24]
 && RefinementVector[25];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__3__24_25_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__3__24_25);
property IDLE__pairing__IDLE_wait_p_sequence__3__24_25;
 IDLE_wait_p_sequence
|->
 ##1 RefinementVector[24]
 && RefinementVector[25];
endproperty

//IDLE_wait_p_sequence
//pair: {25,27}
IDLE__pairing__IDLE_wait_p_sequence__0__25_27_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__0__25_27);
property IDLE__pairing__IDLE_wait_p_sequence__0__25_27;
 IDLE_wait_p_sequence
|->
 ##1 !RefinementVector[25]
 && !RefinementVector[27];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__1__25_27_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__1__25_27);
property IDLE__pairing__IDLE_wait_p_sequence__1__25_27;
 IDLE_wait_p_sequence
|->
 ##1 RefinementVector[25]
 && !RefinementVector[27];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__2__25_27_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__2__25_27);
property IDLE__pairing__IDLE_wait_p_sequence__2__25_27;
 IDLE_wait_p_sequence
|->
 ##1 !RefinementVector[25]
 && RefinementVector[27];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__3__25_27_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__3__25_27);
property IDLE__pairing__IDLE_wait_p_sequence__3__25_27;
 IDLE_wait_p_sequence
|->
 ##1 RefinementVector[25]
 && RefinementVector[27];
endproperty

//IDLE_wait_p_sequence
//pair: {27,30}
IDLE__pairing__IDLE_wait_p_sequence__0__27_30_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__0__27_30);
property IDLE__pairing__IDLE_wait_p_sequence__0__27_30;
 IDLE_wait_p_sequence
|->
 ##1 !RefinementVector[27]
 && !RefinementVector[30];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__1__27_30_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__1__27_30);
property IDLE__pairing__IDLE_wait_p_sequence__1__27_30;
 IDLE_wait_p_sequence
|->
 ##1 RefinementVector[27]
 && !RefinementVector[30];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__2__27_30_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__2__27_30);
property IDLE__pairing__IDLE_wait_p_sequence__2__27_30;
 IDLE_wait_p_sequence
|->
 ##1 !RefinementVector[27]
 && RefinementVector[30];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__3__27_30_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__3__27_30);
property IDLE__pairing__IDLE_wait_p_sequence__3__27_30;
 IDLE_wait_p_sequence
|->
 ##1 RefinementVector[27]
 && RefinementVector[30];
endproperty

//IDLE_wait_p_sequence
//pair: {30,32}
IDLE__pairing__IDLE_wait_p_sequence__0__30_32_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__0__30_32);
property IDLE__pairing__IDLE_wait_p_sequence__0__30_32;
 IDLE_wait_p_sequence
|->
 ##1 !RefinementVector[30]
 && !RefinementVector[32];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__1__30_32_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__1__30_32);
property IDLE__pairing__IDLE_wait_p_sequence__1__30_32;
 IDLE_wait_p_sequence
|->
 ##1 RefinementVector[30]
 && !RefinementVector[32];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__2__30_32_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__2__30_32);
property IDLE__pairing__IDLE_wait_p_sequence__2__30_32;
 IDLE_wait_p_sequence
|->
 ##1 !RefinementVector[30]
 && RefinementVector[32];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__3__30_32_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__3__30_32);
property IDLE__pairing__IDLE_wait_p_sequence__3__30_32;
 IDLE_wait_p_sequence
|->
 ##1 RefinementVector[30]
 && RefinementVector[32];
endproperty

//IDLE_wait_p_sequence
//pair: {32,33}
IDLE__pairing__IDLE_wait_p_sequence__0__32_33_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__0__32_33);
property IDLE__pairing__IDLE_wait_p_sequence__0__32_33;
 IDLE_wait_p_sequence
|->
 ##1 !RefinementVector[32]
 && !RefinementVector[33];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__1__32_33_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__1__32_33);
property IDLE__pairing__IDLE_wait_p_sequence__1__32_33;
 IDLE_wait_p_sequence
|->
 ##1 RefinementVector[32]
 && !RefinementVector[33];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__2__32_33_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__2__32_33);
property IDLE__pairing__IDLE_wait_p_sequence__2__32_33;
 IDLE_wait_p_sequence
|->
 ##1 !RefinementVector[32]
 && RefinementVector[33];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__3__32_33_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__3__32_33);
property IDLE__pairing__IDLE_wait_p_sequence__3__32_33;
 IDLE_wait_p_sequence
|->
 ##1 RefinementVector[32]
 && RefinementVector[33];
endproperty

//IDLE_wait_p_sequence
//pair: {33,35}
IDLE__pairing__IDLE_wait_p_sequence__0__33_35_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__0__33_35);
property IDLE__pairing__IDLE_wait_p_sequence__0__33_35;
 IDLE_wait_p_sequence
|->
 ##1 !RefinementVector[33]
 && !RefinementVector[35];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__1__33_35_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__1__33_35);
property IDLE__pairing__IDLE_wait_p_sequence__1__33_35;
 IDLE_wait_p_sequence
|->
 ##1 RefinementVector[33]
 && !RefinementVector[35];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__2__33_35_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__2__33_35);
property IDLE__pairing__IDLE_wait_p_sequence__2__33_35;
 IDLE_wait_p_sequence
|->
 ##1 !RefinementVector[33]
 && RefinementVector[35];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__3__33_35_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__3__33_35);
property IDLE__pairing__IDLE_wait_p_sequence__3__33_35;
 IDLE_wait_p_sequence
|->
 ##1 RefinementVector[33]
 && RefinementVector[35];
endproperty

//IDLE_wait_p_sequence
//pair: {35,37}
IDLE__pairing__IDLE_wait_p_sequence__0__35_37_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__0__35_37);
property IDLE__pairing__IDLE_wait_p_sequence__0__35_37;
 IDLE_wait_p_sequence
|->
 ##1 !RefinementVector[35]
 && !RefinementVector[37];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__1__35_37_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__1__35_37);
property IDLE__pairing__IDLE_wait_p_sequence__1__35_37;
 IDLE_wait_p_sequence
|->
 ##1 RefinementVector[35]
 && !RefinementVector[37];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__2__35_37_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__2__35_37);
property IDLE__pairing__IDLE_wait_p_sequence__2__35_37;
 IDLE_wait_p_sequence
|->
 ##1 !RefinementVector[35]
 && RefinementVector[37];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__3__35_37_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__3__35_37);
property IDLE__pairing__IDLE_wait_p_sequence__3__35_37;
 IDLE_wait_p_sequence
|->
 ##1 RefinementVector[35]
 && RefinementVector[37];
endproperty

//IDLE_wait_p_sequence
//pair: {37,38}
IDLE__pairing__IDLE_wait_p_sequence__0__37_38_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__0__37_38);
property IDLE__pairing__IDLE_wait_p_sequence__0__37_38;
 IDLE_wait_p_sequence
|->
 ##1 !RefinementVector[37]
 && !RefinementVector[38];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__1__37_38_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__1__37_38);
property IDLE__pairing__IDLE_wait_p_sequence__1__37_38;
 IDLE_wait_p_sequence
|->
 ##1 RefinementVector[37]
 && !RefinementVector[38];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__2__37_38_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__2__37_38);
property IDLE__pairing__IDLE_wait_p_sequence__2__37_38;
 IDLE_wait_p_sequence
|->
 ##1 !RefinementVector[37]
 && RefinementVector[38];
endproperty

IDLE__pairing__IDLE_wait_p_sequence__3__37_38_a: assert property (disable iff(reset_n || zeroize) IDLE__pairing__IDLE_wait_p_sequence__3__37_38);
property IDLE__pairing__IDLE_wait_p_sequence__3__37_38;
 IDLE_wait_p_sequence
|->
 ##1 RefinementVector[37]
 && RefinementVector[38];
endproperty


//reset_p_sequence
//pair: {0,1}
IDLE__pairing__reset_p_sequence__0__0_1_a: assert property (IDLE__pairing__reset_p_sequence__0__0_1);
property IDLE__pairing__reset_p_sequence__0__0_1;
 reset_p_sequence
|->
 !RefinementVector[0]
 && !RefinementVector[1];
endproperty

IDLE__pairing__reset_p_sequence__1__0_1_a: assert property (IDLE__pairing__reset_p_sequence__1__0_1);
property IDLE__pairing__reset_p_sequence__1__0_1;
 reset_p_sequence
|->
 RefinementVector[0]
 && !RefinementVector[1];
endproperty

IDLE__pairing__reset_p_sequence__2__0_1_a: assert property (IDLE__pairing__reset_p_sequence__2__0_1);
property IDLE__pairing__reset_p_sequence__2__0_1;
 reset_p_sequence
|->
 !RefinementVector[0]
 && RefinementVector[1];
endproperty

IDLE__pairing__reset_p_sequence__3__0_1_a: assert property (IDLE__pairing__reset_p_sequence__3__0_1);
property IDLE__pairing__reset_p_sequence__3__0_1;
 reset_p_sequence
|->
 RefinementVector[0]
 && RefinementVector[1];
endproperty

//reset_p_sequence
//pair: {1,2}
IDLE__pairing__reset_p_sequence__0__1_2_a: assert property (IDLE__pairing__reset_p_sequence__0__1_2);
property IDLE__pairing__reset_p_sequence__0__1_2;
 reset_p_sequence
|->
 !RefinementVector[1]
 && !RefinementVector[2];
endproperty

IDLE__pairing__reset_p_sequence__1__1_2_a: assert property (IDLE__pairing__reset_p_sequence__1__1_2);
property IDLE__pairing__reset_p_sequence__1__1_2;
 reset_p_sequence
|->
 RefinementVector[1]
 && !RefinementVector[2];
endproperty

IDLE__pairing__reset_p_sequence__2__1_2_a: assert property (IDLE__pairing__reset_p_sequence__2__1_2);
property IDLE__pairing__reset_p_sequence__2__1_2;
 reset_p_sequence
|->
 !RefinementVector[1]
 && RefinementVector[2];
endproperty

IDLE__pairing__reset_p_sequence__3__1_2_a: assert property (IDLE__pairing__reset_p_sequence__3__1_2);
property IDLE__pairing__reset_p_sequence__3__1_2;
 reset_p_sequence
|->
 RefinementVector[1]
 && RefinementVector[2];
endproperty

//reset_p_sequence
//pair: {2,3}
IDLE__pairing__reset_p_sequence__0__2_3_a: assert property (IDLE__pairing__reset_p_sequence__0__2_3);
property IDLE__pairing__reset_p_sequence__0__2_3;
 reset_p_sequence
|->
 !RefinementVector[2]
 && !RefinementVector[3];
endproperty

IDLE__pairing__reset_p_sequence__1__2_3_a: assert property (IDLE__pairing__reset_p_sequence__1__2_3);
property IDLE__pairing__reset_p_sequence__1__2_3;
 reset_p_sequence
|->
 RefinementVector[2]
 && !RefinementVector[3];
endproperty

IDLE__pairing__reset_p_sequence__2__2_3_a: assert property (IDLE__pairing__reset_p_sequence__2__2_3);
property IDLE__pairing__reset_p_sequence__2__2_3;
 reset_p_sequence
|->
 !RefinementVector[2]
 && RefinementVector[3];
endproperty

IDLE__pairing__reset_p_sequence__3__2_3_a: assert property (IDLE__pairing__reset_p_sequence__3__2_3);
property IDLE__pairing__reset_p_sequence__3__2_3;
 reset_p_sequence
|->
 RefinementVector[2]
 && RefinementVector[3];
endproperty

//reset_p_sequence
//pair: {3,19}
IDLE__pairing__reset_p_sequence__0__3_19_a: assert property (IDLE__pairing__reset_p_sequence__0__3_19);
property IDLE__pairing__reset_p_sequence__0__3_19;
 reset_p_sequence
|->
 !RefinementVector[3]
 && !RefinementVector[19];
endproperty

IDLE__pairing__reset_p_sequence__1__3_19_a: assert property (IDLE__pairing__reset_p_sequence__1__3_19);
property IDLE__pairing__reset_p_sequence__1__3_19;
 reset_p_sequence
|->
 RefinementVector[3]
 && !RefinementVector[19];
endproperty

IDLE__pairing__reset_p_sequence__2__3_19_a: assert property (IDLE__pairing__reset_p_sequence__2__3_19);
property IDLE__pairing__reset_p_sequence__2__3_19;
 reset_p_sequence
|->
 !RefinementVector[3]
 && RefinementVector[19];
endproperty

IDLE__pairing__reset_p_sequence__3__3_19_a: assert property (IDLE__pairing__reset_p_sequence__3__3_19);
property IDLE__pairing__reset_p_sequence__3__3_19;
 reset_p_sequence
|->
 RefinementVector[3]
 && RefinementVector[19];
endproperty

//reset_p_sequence
//pair: {19,21}
IDLE__pairing__reset_p_sequence__0__19_21_a: assert property (IDLE__pairing__reset_p_sequence__0__19_21);
property IDLE__pairing__reset_p_sequence__0__19_21;
 reset_p_sequence
|->
 !RefinementVector[19]
 && !RefinementVector[21];
endproperty

IDLE__pairing__reset_p_sequence__1__19_21_a: assert property (IDLE__pairing__reset_p_sequence__1__19_21);
property IDLE__pairing__reset_p_sequence__1__19_21;
 reset_p_sequence
|->
 RefinementVector[19]
 && !RefinementVector[21];
endproperty

IDLE__pairing__reset_p_sequence__2__19_21_a: assert property (IDLE__pairing__reset_p_sequence__2__19_21);
property IDLE__pairing__reset_p_sequence__2__19_21;
 reset_p_sequence
|->
 !RefinementVector[19]
 && RefinementVector[21];
endproperty

IDLE__pairing__reset_p_sequence__3__19_21_a: assert property (IDLE__pairing__reset_p_sequence__3__19_21);
property IDLE__pairing__reset_p_sequence__3__19_21;
 reset_p_sequence
|->
 RefinementVector[19]
 && RefinementVector[21];
endproperty

//reset_p_sequence
//pair: {21,24}
IDLE__pairing__reset_p_sequence__0__21_24_a: assert property (IDLE__pairing__reset_p_sequence__0__21_24);
property IDLE__pairing__reset_p_sequence__0__21_24;
 reset_p_sequence
|->
 !RefinementVector[21]
 && !RefinementVector[24];
endproperty

IDLE__pairing__reset_p_sequence__1__21_24_a: assert property (IDLE__pairing__reset_p_sequence__1__21_24);
property IDLE__pairing__reset_p_sequence__1__21_24;
 reset_p_sequence
|->
 RefinementVector[21]
 && !RefinementVector[24];
endproperty

IDLE__pairing__reset_p_sequence__2__21_24_a: assert property (IDLE__pairing__reset_p_sequence__2__21_24);
property IDLE__pairing__reset_p_sequence__2__21_24;
 reset_p_sequence
|->
 !RefinementVector[21]
 && RefinementVector[24];
endproperty

IDLE__pairing__reset_p_sequence__3__21_24_a: assert property (IDLE__pairing__reset_p_sequence__3__21_24);
property IDLE__pairing__reset_p_sequence__3__21_24;
 reset_p_sequence
|->
 RefinementVector[21]
 && RefinementVector[24];
endproperty

//reset_p_sequence
//pair: {24,27}
IDLE__pairing__reset_p_sequence__0__24_27_a: assert property (IDLE__pairing__reset_p_sequence__0__24_27);
property IDLE__pairing__reset_p_sequence__0__24_27;
 reset_p_sequence
|->
 !RefinementVector[24]
 && !RefinementVector[27];
endproperty

IDLE__pairing__reset_p_sequence__1__24_27_a: assert property (IDLE__pairing__reset_p_sequence__1__24_27);
property IDLE__pairing__reset_p_sequence__1__24_27;
 reset_p_sequence
|->
 RefinementVector[24]
 && !RefinementVector[27];
endproperty

IDLE__pairing__reset_p_sequence__2__24_27_a: assert property (IDLE__pairing__reset_p_sequence__2__24_27);
property IDLE__pairing__reset_p_sequence__2__24_27;
 reset_p_sequence
|->
 !RefinementVector[24]
 && RefinementVector[27];
endproperty

IDLE__pairing__reset_p_sequence__3__24_27_a: assert property (IDLE__pairing__reset_p_sequence__3__24_27);
property IDLE__pairing__reset_p_sequence__3__24_27;
 reset_p_sequence
|->
 RefinementVector[24]
 && RefinementVector[27];
endproperty

//reset_p_sequence
//pair: {27,30}
IDLE__pairing__reset_p_sequence__0__27_30_a: assert property (IDLE__pairing__reset_p_sequence__0__27_30);
property IDLE__pairing__reset_p_sequence__0__27_30;
 reset_p_sequence
|->
 !RefinementVector[27]
 && !RefinementVector[30];
endproperty

IDLE__pairing__reset_p_sequence__1__27_30_a: assert property (IDLE__pairing__reset_p_sequence__1__27_30);
property IDLE__pairing__reset_p_sequence__1__27_30;
 reset_p_sequence
|->
 RefinementVector[27]
 && !RefinementVector[30];
endproperty

IDLE__pairing__reset_p_sequence__2__27_30_a: assert property (IDLE__pairing__reset_p_sequence__2__27_30);
property IDLE__pairing__reset_p_sequence__2__27_30;
 reset_p_sequence
|->
 !RefinementVector[27]
 && RefinementVector[30];
endproperty

IDLE__pairing__reset_p_sequence__3__27_30_a: assert property (IDLE__pairing__reset_p_sequence__3__27_30);
property IDLE__pairing__reset_p_sequence__3__27_30;
 reset_p_sequence
|->
 RefinementVector[27]
 && RefinementVector[30];
endproperty

//reset_p_sequence
//pair: {30,32}
IDLE__pairing__reset_p_sequence__0__30_32_a: assert property (IDLE__pairing__reset_p_sequence__0__30_32);
property IDLE__pairing__reset_p_sequence__0__30_32;
 reset_p_sequence
|->
 !RefinementVector[30]
 && !RefinementVector[32];
endproperty

IDLE__pairing__reset_p_sequence__1__30_32_a: assert property (IDLE__pairing__reset_p_sequence__1__30_32);
property IDLE__pairing__reset_p_sequence__1__30_32;
 reset_p_sequence
|->
 RefinementVector[30]
 && !RefinementVector[32];
endproperty

IDLE__pairing__reset_p_sequence__2__30_32_a: assert property (IDLE__pairing__reset_p_sequence__2__30_32);
property IDLE__pairing__reset_p_sequence__2__30_32;
 reset_p_sequence
|->
 !RefinementVector[30]
 && RefinementVector[32];
endproperty

IDLE__pairing__reset_p_sequence__3__30_32_a: assert property (IDLE__pairing__reset_p_sequence__3__30_32);
property IDLE__pairing__reset_p_sequence__3__30_32;
 reset_p_sequence
|->
 RefinementVector[30]
 && RefinementVector[32];
endproperty

//reset_p_sequence
//pair: {32,33}
IDLE__pairing__reset_p_sequence__0__32_33_a: assert property (IDLE__pairing__reset_p_sequence__0__32_33);
property IDLE__pairing__reset_p_sequence__0__32_33;
 reset_p_sequence
|->
 !RefinementVector[32]
 && !RefinementVector[33];
endproperty

IDLE__pairing__reset_p_sequence__1__32_33_a: assert property (IDLE__pairing__reset_p_sequence__1__32_33);
property IDLE__pairing__reset_p_sequence__1__32_33;
 reset_p_sequence
|->
 RefinementVector[32]
 && !RefinementVector[33];
endproperty

IDLE__pairing__reset_p_sequence__2__32_33_a: assert property (IDLE__pairing__reset_p_sequence__2__32_33);
property IDLE__pairing__reset_p_sequence__2__32_33;
 reset_p_sequence
|->
 !RefinementVector[32]
 && RefinementVector[33];
endproperty

IDLE__pairing__reset_p_sequence__3__32_33_a: assert property (IDLE__pairing__reset_p_sequence__3__32_33);
property IDLE__pairing__reset_p_sequence__3__32_33;
 reset_p_sequence
|->
 RefinementVector[32]
 && RefinementVector[33];
endproperty

//reset_p_sequence
//pair: {33,35}
IDLE__pairing__reset_p_sequence__0__33_35_a: assert property (IDLE__pairing__reset_p_sequence__0__33_35);
property IDLE__pairing__reset_p_sequence__0__33_35;
 reset_p_sequence
|->
 !RefinementVector[33]
 && !RefinementVector[35];
endproperty

IDLE__pairing__reset_p_sequence__1__33_35_a: assert property (IDLE__pairing__reset_p_sequence__1__33_35);
property IDLE__pairing__reset_p_sequence__1__33_35;
 reset_p_sequence
|->
 RefinementVector[33]
 && !RefinementVector[35];
endproperty

IDLE__pairing__reset_p_sequence__2__33_35_a: assert property (IDLE__pairing__reset_p_sequence__2__33_35);
property IDLE__pairing__reset_p_sequence__2__33_35;
 reset_p_sequence
|->
 !RefinementVector[33]
 && RefinementVector[35];
endproperty

IDLE__pairing__reset_p_sequence__3__33_35_a: assert property (IDLE__pairing__reset_p_sequence__3__33_35);
property IDLE__pairing__reset_p_sequence__3__33_35;
 reset_p_sequence
|->
 RefinementVector[33]
 && RefinementVector[35];
endproperty

//reset_p_sequence
//pair: {35,37}
IDLE__pairing__reset_p_sequence__0__35_37_a: assert property (IDLE__pairing__reset_p_sequence__0__35_37);
property IDLE__pairing__reset_p_sequence__0__35_37;
 reset_p_sequence
|->
 !RefinementVector[35]
 && !RefinementVector[37];
endproperty

IDLE__pairing__reset_p_sequence__1__35_37_a: assert property (IDLE__pairing__reset_p_sequence__1__35_37);
property IDLE__pairing__reset_p_sequence__1__35_37;
 reset_p_sequence
|->
 RefinementVector[35]
 && !RefinementVector[37];
endproperty

IDLE__pairing__reset_p_sequence__2__35_37_a: assert property (IDLE__pairing__reset_p_sequence__2__35_37);
property IDLE__pairing__reset_p_sequence__2__35_37;
 reset_p_sequence
|->
 !RefinementVector[35]
 && RefinementVector[37];
endproperty

IDLE__pairing__reset_p_sequence__3__35_37_a: assert property (IDLE__pairing__reset_p_sequence__3__35_37);
property IDLE__pairing__reset_p_sequence__3__35_37;
 reset_p_sequence
|->
 RefinementVector[35]
 && RefinementVector[37];
endproperty

//reset_p_sequence
//pair: {37,38}
IDLE__pairing__reset_p_sequence__0__37_38_a: assert property (IDLE__pairing__reset_p_sequence__0__37_38);
property IDLE__pairing__reset_p_sequence__0__37_38;
 reset_p_sequence
|->
 !RefinementVector[37]
 && !RefinementVector[38];
endproperty

IDLE__pairing__reset_p_sequence__1__37_38_a: assert property (IDLE__pairing__reset_p_sequence__1__37_38);
property IDLE__pairing__reset_p_sequence__1__37_38;
 reset_p_sequence
|->
 RefinementVector[37]
 && !RefinementVector[38];
endproperty

IDLE__pairing__reset_p_sequence__2__37_38_a: assert property (IDLE__pairing__reset_p_sequence__2__37_38);
property IDLE__pairing__reset_p_sequence__2__37_38;
 reset_p_sequence
|->
 !RefinementVector[37]
 && RefinementVector[38];
endproperty

IDLE__pairing__reset_p_sequence__3__37_38_a: assert property (IDLE__pairing__reset_p_sequence__3__37_38);
property IDLE__pairing__reset_p_sequence__3__37_38;
 reset_p_sequence
|->
 RefinementVector[37]
 && RefinementVector[38];
endproperty


/******************************************/
/* SHARounds state bit-pairing properties */
/******************************************/

//IDLE_to_SHARounds_1_p_sequence
//pair: {0,1}
SHARounds__pairing__IDLE_to_SHARounds_1_p_sequence__0__0_1_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_1_p_sequence__0__0_1);
property SHARounds__pairing__IDLE_to_SHARounds_1_p_sequence__0__0_1;
 IDLE_to_SHARounds_1_p_sequence
|->
 ##1 !RefinementVector[0]
 && !RefinementVector[1];
endproperty

SHARounds__pairing__IDLE_to_SHARounds_1_p_sequence__1__0_1_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_1_p_sequence__1__0_1);
property SHARounds__pairing__IDLE_to_SHARounds_1_p_sequence__1__0_1;
 IDLE_to_SHARounds_1_p_sequence
|->
 ##1 RefinementVector[0]
 && !RefinementVector[1];
endproperty

SHARounds__pairing__IDLE_to_SHARounds_1_p_sequence__2__0_1_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_1_p_sequence__2__0_1);
property SHARounds__pairing__IDLE_to_SHARounds_1_p_sequence__2__0_1;
 IDLE_to_SHARounds_1_p_sequence
|->
 ##1 !RefinementVector[0]
 && RefinementVector[1];
endproperty

SHARounds__pairing__IDLE_to_SHARounds_1_p_sequence__3__0_1_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_1_p_sequence__3__0_1);
property SHARounds__pairing__IDLE_to_SHARounds_1_p_sequence__3__0_1;
 IDLE_to_SHARounds_1_p_sequence
|->
 ##1 RefinementVector[0]
 && RefinementVector[1];
endproperty

//IDLE_to_SHARounds_1_p_sequence
//pair: {1,2}
SHARounds__pairing__IDLE_to_SHARounds_1_p_sequence__0__1_2_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_1_p_sequence__0__1_2);
property SHARounds__pairing__IDLE_to_SHARounds_1_p_sequence__0__1_2;
 IDLE_to_SHARounds_1_p_sequence
|->
 ##1 !RefinementVector[1]
 && !RefinementVector[2];
endproperty

SHARounds__pairing__IDLE_to_SHARounds_1_p_sequence__1__1_2_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_1_p_sequence__1__1_2);
property SHARounds__pairing__IDLE_to_SHARounds_1_p_sequence__1__1_2;
 IDLE_to_SHARounds_1_p_sequence
|->
 ##1 RefinementVector[1]
 && !RefinementVector[2];
endproperty

SHARounds__pairing__IDLE_to_SHARounds_1_p_sequence__2__1_2_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_1_p_sequence__2__1_2);
property SHARounds__pairing__IDLE_to_SHARounds_1_p_sequence__2__1_2;
 IDLE_to_SHARounds_1_p_sequence
|->
 ##1 !RefinementVector[1]
 && RefinementVector[2];
endproperty

SHARounds__pairing__IDLE_to_SHARounds_1_p_sequence__3__1_2_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_1_p_sequence__3__1_2);
property SHARounds__pairing__IDLE_to_SHARounds_1_p_sequence__3__1_2;
 IDLE_to_SHARounds_1_p_sequence
|->
 ##1 RefinementVector[1]
 && RefinementVector[2];
endproperty

//IDLE_to_SHARounds_1_p_sequence
//pair: {2,3}
SHARounds__pairing__IDLE_to_SHARounds_1_p_sequence__0__2_3_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_1_p_sequence__0__2_3);
property SHARounds__pairing__IDLE_to_SHARounds_1_p_sequence__0__2_3;
 IDLE_to_SHARounds_1_p_sequence
|->
 ##1 !RefinementVector[2]
 && !RefinementVector[3];
endproperty

SHARounds__pairing__IDLE_to_SHARounds_1_p_sequence__1__2_3_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_1_p_sequence__1__2_3);
property SHARounds__pairing__IDLE_to_SHARounds_1_p_sequence__1__2_3;
 IDLE_to_SHARounds_1_p_sequence
|->
 ##1 RefinementVector[2]
 && !RefinementVector[3];
endproperty

SHARounds__pairing__IDLE_to_SHARounds_1_p_sequence__2__2_3_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_1_p_sequence__2__2_3);
property SHARounds__pairing__IDLE_to_SHARounds_1_p_sequence__2__2_3;
 IDLE_to_SHARounds_1_p_sequence
|->
 ##1 !RefinementVector[2]
 && RefinementVector[3];
endproperty

SHARounds__pairing__IDLE_to_SHARounds_1_p_sequence__3__2_3_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_1_p_sequence__3__2_3);
property SHARounds__pairing__IDLE_to_SHARounds_1_p_sequence__3__2_3;
 IDLE_to_SHARounds_1_p_sequence
|->
 ##1 RefinementVector[2]
 && RefinementVector[3];
endproperty


//IDLE_to_SHARounds_2_p_sequence
//pair: {0,1}
SHARounds__pairing__IDLE_to_SHARounds_2_p_sequence__0__0_1_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_2_p_sequence__0__0_1);
property SHARounds__pairing__IDLE_to_SHARounds_2_p_sequence__0__0_1;
 IDLE_to_SHARounds_2_p_sequence
|->
 ##1 !RefinementVector[0]
 && !RefinementVector[1];
endproperty

SHARounds__pairing__IDLE_to_SHARounds_2_p_sequence__1__0_1_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_2_p_sequence__1__0_1);
property SHARounds__pairing__IDLE_to_SHARounds_2_p_sequence__1__0_1;
 IDLE_to_SHARounds_2_p_sequence
|->
 ##1 RefinementVector[0]
 && !RefinementVector[1];
endproperty

SHARounds__pairing__IDLE_to_SHARounds_2_p_sequence__2__0_1_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_2_p_sequence__2__0_1);
property SHARounds__pairing__IDLE_to_SHARounds_2_p_sequence__2__0_1;
 IDLE_to_SHARounds_2_p_sequence
|->
 ##1 !RefinementVector[0]
 && RefinementVector[1];
endproperty

SHARounds__pairing__IDLE_to_SHARounds_2_p_sequence__3__0_1_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_2_p_sequence__3__0_1);
property SHARounds__pairing__IDLE_to_SHARounds_2_p_sequence__3__0_1;
 IDLE_to_SHARounds_2_p_sequence
|->
 ##1 RefinementVector[0]
 && RefinementVector[1];
endproperty

//IDLE_to_SHARounds_2_p_sequence
//pair: {1,2}
SHARounds__pairing__IDLE_to_SHARounds_2_p_sequence__0__1_2_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_2_p_sequence__0__1_2);
property SHARounds__pairing__IDLE_to_SHARounds_2_p_sequence__0__1_2;
 IDLE_to_SHARounds_2_p_sequence
|->
 ##1 !RefinementVector[1]
 && !RefinementVector[2];
endproperty

SHARounds__pairing__IDLE_to_SHARounds_2_p_sequence__1__1_2_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_2_p_sequence__1__1_2);
property SHARounds__pairing__IDLE_to_SHARounds_2_p_sequence__1__1_2;
 IDLE_to_SHARounds_2_p_sequence
|->
 ##1 RefinementVector[1]
 && !RefinementVector[2];
endproperty

SHARounds__pairing__IDLE_to_SHARounds_2_p_sequence__2__1_2_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_2_p_sequence__2__1_2);
property SHARounds__pairing__IDLE_to_SHARounds_2_p_sequence__2__1_2;
 IDLE_to_SHARounds_2_p_sequence
|->
 ##1 !RefinementVector[1]
 && RefinementVector[2];
endproperty

SHARounds__pairing__IDLE_to_SHARounds_2_p_sequence__3__1_2_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_2_p_sequence__3__1_2);
property SHARounds__pairing__IDLE_to_SHARounds_2_p_sequence__3__1_2;
 IDLE_to_SHARounds_2_p_sequence
|->
 ##1 RefinementVector[1]
 && RefinementVector[2];
endproperty

//IDLE_to_SHARounds_2_p_sequence
//pair: {2,3}
SHARounds__pairing__IDLE_to_SHARounds_2_p_sequence__0__2_3_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_2_p_sequence__0__2_3);
property SHARounds__pairing__IDLE_to_SHARounds_2_p_sequence__0__2_3;
 IDLE_to_SHARounds_2_p_sequence
|->
 ##1 !RefinementVector[2]
 && !RefinementVector[3];
endproperty

SHARounds__pairing__IDLE_to_SHARounds_2_p_sequence__1__2_3_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_2_p_sequence__1__2_3);
property SHARounds__pairing__IDLE_to_SHARounds_2_p_sequence__1__2_3;
 IDLE_to_SHARounds_2_p_sequence
|->
 ##1 RefinementVector[2]
 && !RefinementVector[3];
endproperty

SHARounds__pairing__IDLE_to_SHARounds_2_p_sequence__2__2_3_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_2_p_sequence__2__2_3);
property SHARounds__pairing__IDLE_to_SHARounds_2_p_sequence__2__2_3;
 IDLE_to_SHARounds_2_p_sequence
|->
 ##1 !RefinementVector[2]
 && RefinementVector[3];
endproperty

SHARounds__pairing__IDLE_to_SHARounds_2_p_sequence__3__2_3_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_2_p_sequence__3__2_3);
property SHARounds__pairing__IDLE_to_SHARounds_2_p_sequence__3__2_3;
 IDLE_to_SHARounds_2_p_sequence
|->
 ##1 RefinementVector[2]
 && RefinementVector[3];
endproperty


//IDLE_to_SHARounds_3_p_sequence
//pair: {0,1}
SHARounds__pairing__IDLE_to_SHARounds_3_p_sequence__0__0_1_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_3_p_sequence__0__0_1);
property SHARounds__pairing__IDLE_to_SHARounds_3_p_sequence__0__0_1;
 IDLE_to_SHARounds_3_p_sequence
|->
 ##1 !RefinementVector[0]
 && !RefinementVector[1];
endproperty

SHARounds__pairing__IDLE_to_SHARounds_3_p_sequence__1__0_1_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_3_p_sequence__1__0_1);
property SHARounds__pairing__IDLE_to_SHARounds_3_p_sequence__1__0_1;
 IDLE_to_SHARounds_3_p_sequence
|->
 ##1 RefinementVector[0]
 && !RefinementVector[1];
endproperty

SHARounds__pairing__IDLE_to_SHARounds_3_p_sequence__2__0_1_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_3_p_sequence__2__0_1);
property SHARounds__pairing__IDLE_to_SHARounds_3_p_sequence__2__0_1;
 IDLE_to_SHARounds_3_p_sequence
|->
 ##1 !RefinementVector[0]
 && RefinementVector[1];
endproperty

SHARounds__pairing__IDLE_to_SHARounds_3_p_sequence__3__0_1_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_3_p_sequence__3__0_1);
property SHARounds__pairing__IDLE_to_SHARounds_3_p_sequence__3__0_1;
 IDLE_to_SHARounds_3_p_sequence
|->
 ##1 RefinementVector[0]
 && RefinementVector[1];
endproperty

//IDLE_to_SHARounds_3_p_sequence
//pair: {1,2}
SHARounds__pairing__IDLE_to_SHARounds_3_p_sequence__0__1_2_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_3_p_sequence__0__1_2);
property SHARounds__pairing__IDLE_to_SHARounds_3_p_sequence__0__1_2;
 IDLE_to_SHARounds_3_p_sequence
|->
 ##1 !RefinementVector[1]
 && !RefinementVector[2];
endproperty

SHARounds__pairing__IDLE_to_SHARounds_3_p_sequence__1__1_2_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_3_p_sequence__1__1_2);
property SHARounds__pairing__IDLE_to_SHARounds_3_p_sequence__1__1_2;
 IDLE_to_SHARounds_3_p_sequence
|->
 ##1 RefinementVector[1]
 && !RefinementVector[2];
endproperty

SHARounds__pairing__IDLE_to_SHARounds_3_p_sequence__2__1_2_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_3_p_sequence__2__1_2);
property SHARounds__pairing__IDLE_to_SHARounds_3_p_sequence__2__1_2;
 IDLE_to_SHARounds_3_p_sequence
|->
 ##1 !RefinementVector[1]
 && RefinementVector[2];
endproperty

SHARounds__pairing__IDLE_to_SHARounds_3_p_sequence__3__1_2_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_3_p_sequence__3__1_2);
property SHARounds__pairing__IDLE_to_SHARounds_3_p_sequence__3__1_2;
 IDLE_to_SHARounds_3_p_sequence
|->
 ##1 RefinementVector[1]
 && RefinementVector[2];
endproperty

//IDLE_to_SHARounds_3_p_sequence
//pair: {2,3}
SHARounds__pairing__IDLE_to_SHARounds_3_p_sequence__0__2_3_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_3_p_sequence__0__2_3);
property SHARounds__pairing__IDLE_to_SHARounds_3_p_sequence__0__2_3;
 IDLE_to_SHARounds_3_p_sequence
|->
 ##1 !RefinementVector[2]
 && !RefinementVector[3];
endproperty

SHARounds__pairing__IDLE_to_SHARounds_3_p_sequence__1__2_3_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_3_p_sequence__1__2_3);
property SHARounds__pairing__IDLE_to_SHARounds_3_p_sequence__1__2_3;
 IDLE_to_SHARounds_3_p_sequence
|->
 ##1 RefinementVector[2]
 && !RefinementVector[3];
endproperty

SHARounds__pairing__IDLE_to_SHARounds_3_p_sequence__2__2_3_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_3_p_sequence__2__2_3);
property SHARounds__pairing__IDLE_to_SHARounds_3_p_sequence__2__2_3;
 IDLE_to_SHARounds_3_p_sequence
|->
 ##1 !RefinementVector[2]
 && RefinementVector[3];
endproperty

SHARounds__pairing__IDLE_to_SHARounds_3_p_sequence__3__2_3_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_3_p_sequence__3__2_3);
property SHARounds__pairing__IDLE_to_SHARounds_3_p_sequence__3__2_3;
 IDLE_to_SHARounds_3_p_sequence
|->
 ##1 RefinementVector[2]
 && RefinementVector[3];
endproperty


//IDLE_to_SHARounds_4_p_sequence
//pair: {0,1}
SHARounds__pairing__IDLE_to_SHARounds_4_p_sequence__0__0_1_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_4_p_sequence__0__0_1);
property SHARounds__pairing__IDLE_to_SHARounds_4_p_sequence__0__0_1;
 IDLE_to_SHARounds_4_p_sequence
|->
 ##1 !RefinementVector[0]
 && !RefinementVector[1];
endproperty

SHARounds__pairing__IDLE_to_SHARounds_4_p_sequence__1__0_1_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_4_p_sequence__1__0_1);
property SHARounds__pairing__IDLE_to_SHARounds_4_p_sequence__1__0_1;
 IDLE_to_SHARounds_4_p_sequence
|->
 ##1 RefinementVector[0]
 && !RefinementVector[1];
endproperty

SHARounds__pairing__IDLE_to_SHARounds_4_p_sequence__2__0_1_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_4_p_sequence__2__0_1);
property SHARounds__pairing__IDLE_to_SHARounds_4_p_sequence__2__0_1;
 IDLE_to_SHARounds_4_p_sequence
|->
 ##1 !RefinementVector[0]
 && RefinementVector[1];
endproperty

SHARounds__pairing__IDLE_to_SHARounds_4_p_sequence__3__0_1_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_4_p_sequence__3__0_1);
property SHARounds__pairing__IDLE_to_SHARounds_4_p_sequence__3__0_1;
 IDLE_to_SHARounds_4_p_sequence
|->
 ##1 RefinementVector[0]
 && RefinementVector[1];
endproperty

//IDLE_to_SHARounds_4_p_sequence
//pair: {1,2}
SHARounds__pairing__IDLE_to_SHARounds_4_p_sequence__0__1_2_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_4_p_sequence__0__1_2);
property SHARounds__pairing__IDLE_to_SHARounds_4_p_sequence__0__1_2;
 IDLE_to_SHARounds_4_p_sequence
|->
 ##1 !RefinementVector[1]
 && !RefinementVector[2];
endproperty

SHARounds__pairing__IDLE_to_SHARounds_4_p_sequence__1__1_2_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_4_p_sequence__1__1_2);
property SHARounds__pairing__IDLE_to_SHARounds_4_p_sequence__1__1_2;
 IDLE_to_SHARounds_4_p_sequence
|->
 ##1 RefinementVector[1]
 && !RefinementVector[2];
endproperty

SHARounds__pairing__IDLE_to_SHARounds_4_p_sequence__2__1_2_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_4_p_sequence__2__1_2);
property SHARounds__pairing__IDLE_to_SHARounds_4_p_sequence__2__1_2;
 IDLE_to_SHARounds_4_p_sequence
|->
 ##1 !RefinementVector[1]
 && RefinementVector[2];
endproperty

SHARounds__pairing__IDLE_to_SHARounds_4_p_sequence__3__1_2_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_4_p_sequence__3__1_2);
property SHARounds__pairing__IDLE_to_SHARounds_4_p_sequence__3__1_2;
 IDLE_to_SHARounds_4_p_sequence
|->
 ##1 RefinementVector[1]
 && RefinementVector[2];
endproperty

//IDLE_to_SHARounds_4_p_sequence
//pair: {2,3}
SHARounds__pairing__IDLE_to_SHARounds_4_p_sequence__0__2_3_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_4_p_sequence__0__2_3);
property SHARounds__pairing__IDLE_to_SHARounds_4_p_sequence__0__2_3;
 IDLE_to_SHARounds_4_p_sequence
|->
 ##1 !RefinementVector[2]
 && !RefinementVector[3];
endproperty

SHARounds__pairing__IDLE_to_SHARounds_4_p_sequence__1__2_3_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_4_p_sequence__1__2_3);
property SHARounds__pairing__IDLE_to_SHARounds_4_p_sequence__1__2_3;
 IDLE_to_SHARounds_4_p_sequence
|->
 ##1 RefinementVector[2]
 && !RefinementVector[3];
endproperty

SHARounds__pairing__IDLE_to_SHARounds_4_p_sequence__2__2_3_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_4_p_sequence__2__2_3);
property SHARounds__pairing__IDLE_to_SHARounds_4_p_sequence__2__2_3;
 IDLE_to_SHARounds_4_p_sequence
|->
 ##1 !RefinementVector[2]
 && RefinementVector[3];
endproperty

SHARounds__pairing__IDLE_to_SHARounds_4_p_sequence__3__2_3_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_4_p_sequence__3__2_3);
property SHARounds__pairing__IDLE_to_SHARounds_4_p_sequence__3__2_3;
 IDLE_to_SHARounds_4_p_sequence
|->
 ##1 RefinementVector[2]
 && RefinementVector[3];
endproperty


//IDLE_to_SHARounds_p_sequence
//pair: {0,1}
SHARounds__pairing__IDLE_to_SHARounds_p_sequence__0__0_1_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_p_sequence__0__0_1);
property SHARounds__pairing__IDLE_to_SHARounds_p_sequence__0__0_1;
 IDLE_to_SHARounds_p_sequence
|->
 ##1 !RefinementVector[0]
 && !RefinementVector[1];
endproperty

SHARounds__pairing__IDLE_to_SHARounds_p_sequence__1__0_1_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_p_sequence__1__0_1);
property SHARounds__pairing__IDLE_to_SHARounds_p_sequence__1__0_1;
 IDLE_to_SHARounds_p_sequence
|->
 ##1 RefinementVector[0]
 && !RefinementVector[1];
endproperty

SHARounds__pairing__IDLE_to_SHARounds_p_sequence__2__0_1_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_p_sequence__2__0_1);
property SHARounds__pairing__IDLE_to_SHARounds_p_sequence__2__0_1;
 IDLE_to_SHARounds_p_sequence
|->
 ##1 !RefinementVector[0]
 && RefinementVector[1];
endproperty

SHARounds__pairing__IDLE_to_SHARounds_p_sequence__3__0_1_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_p_sequence__3__0_1);
property SHARounds__pairing__IDLE_to_SHARounds_p_sequence__3__0_1;
 IDLE_to_SHARounds_p_sequence
|->
 ##1 RefinementVector[0]
 && RefinementVector[1];
endproperty

//IDLE_to_SHARounds_p_sequence
//pair: {1,2}
SHARounds__pairing__IDLE_to_SHARounds_p_sequence__0__1_2_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_p_sequence__0__1_2);
property SHARounds__pairing__IDLE_to_SHARounds_p_sequence__0__1_2;
 IDLE_to_SHARounds_p_sequence
|->
 ##1 !RefinementVector[1]
 && !RefinementVector[2];
endproperty

SHARounds__pairing__IDLE_to_SHARounds_p_sequence__1__1_2_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_p_sequence__1__1_2);
property SHARounds__pairing__IDLE_to_SHARounds_p_sequence__1__1_2;
 IDLE_to_SHARounds_p_sequence
|->
 ##1 RefinementVector[1]
 && !RefinementVector[2];
endproperty

SHARounds__pairing__IDLE_to_SHARounds_p_sequence__2__1_2_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_p_sequence__2__1_2);
property SHARounds__pairing__IDLE_to_SHARounds_p_sequence__2__1_2;
 IDLE_to_SHARounds_p_sequence
|->
 ##1 !RefinementVector[1]
 && RefinementVector[2];
endproperty

SHARounds__pairing__IDLE_to_SHARounds_p_sequence__3__1_2_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_p_sequence__3__1_2);
property SHARounds__pairing__IDLE_to_SHARounds_p_sequence__3__1_2;
 IDLE_to_SHARounds_p_sequence
|->
 ##1 RefinementVector[1]
 && RefinementVector[2];
endproperty

//IDLE_to_SHARounds_p_sequence
//pair: {2,3}
SHARounds__pairing__IDLE_to_SHARounds_p_sequence__0__2_3_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_p_sequence__0__2_3);
property SHARounds__pairing__IDLE_to_SHARounds_p_sequence__0__2_3;
 IDLE_to_SHARounds_p_sequence
|->
 ##1 !RefinementVector[2]
 && !RefinementVector[3];
endproperty

SHARounds__pairing__IDLE_to_SHARounds_p_sequence__1__2_3_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_p_sequence__1__2_3);
property SHARounds__pairing__IDLE_to_SHARounds_p_sequence__1__2_3;
 IDLE_to_SHARounds_p_sequence
|->
 ##1 RefinementVector[2]
 && !RefinementVector[3];
endproperty

SHARounds__pairing__IDLE_to_SHARounds_p_sequence__2__2_3_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_p_sequence__2__2_3);
property SHARounds__pairing__IDLE_to_SHARounds_p_sequence__2__2_3;
 IDLE_to_SHARounds_p_sequence
|->
 ##1 !RefinementVector[2]
 && RefinementVector[3];
endproperty

SHARounds__pairing__IDLE_to_SHARounds_p_sequence__3__2_3_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__IDLE_to_SHARounds_p_sequence__3__2_3);
property SHARounds__pairing__IDLE_to_SHARounds_p_sequence__3__2_3;
 IDLE_to_SHARounds_p_sequence
|->
 ##1 RefinementVector[2]
 && RefinementVector[3];
endproperty


//SHARounds_to_SHARounds_1_p_sequence
//pair: {0,1}
SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__0_1_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__0_1);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__0_1;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 !RefinementVector[0]
 && !RefinementVector[1];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__0_1_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__0_1);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__0_1;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 RefinementVector[0]
 && !RefinementVector[1];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__0_1_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__0_1);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__0_1;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 !RefinementVector[0]
 && RefinementVector[1];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__0_1_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__0_1);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__0_1;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 RefinementVector[0]
 && RefinementVector[1];
endproperty

//SHARounds_to_SHARounds_1_p_sequence
//pair: {1,2}
SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__1_2_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__1_2);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__1_2;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 !RefinementVector[1]
 && !RefinementVector[2];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__1_2_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__1_2);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__1_2;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 RefinementVector[1]
 && !RefinementVector[2];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__1_2_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__1_2);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__1_2;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 !RefinementVector[1]
 && RefinementVector[2];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__1_2_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__1_2);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__1_2;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 RefinementVector[1]
 && RefinementVector[2];
endproperty

//SHARounds_to_SHARounds_1_p_sequence
//pair: {2,3}
SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__2_3_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__2_3);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__2_3;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 !RefinementVector[2]
 && !RefinementVector[3];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__2_3_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__2_3);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__2_3;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 RefinementVector[2]
 && !RefinementVector[3];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__2_3_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__2_3);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__2_3;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 !RefinementVector[2]
 && RefinementVector[3];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__2_3_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__2_3);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__2_3;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 RefinementVector[2]
 && RefinementVector[3];
endproperty

//SHARounds_to_SHARounds_1_p_sequence
//pair: {3,5}
SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__3_5_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__3_5);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__3_5;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 !RefinementVector[3]
 && !RefinementVector[5];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__3_5_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__3_5);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__3_5;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 RefinementVector[3]
 && !RefinementVector[5];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__3_5_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__3_5);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__3_5;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 !RefinementVector[3]
 && RefinementVector[5];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__3_5_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__3_5);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__3_5;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 RefinementVector[3]
 && RefinementVector[5];
endproperty

//SHARounds_to_SHARounds_1_p_sequence
//pair: {5,6}
SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__5_6_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__5_6);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__5_6;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 !RefinementVector[5]
 && !RefinementVector[6];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__5_6_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__5_6);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__5_6;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 RefinementVector[5]
 && !RefinementVector[6];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__5_6_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__5_6);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__5_6;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 !RefinementVector[5]
 && RefinementVector[6];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__5_6_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__5_6);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__5_6;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 RefinementVector[5]
 && RefinementVector[6];
endproperty

//SHARounds_to_SHARounds_1_p_sequence
//pair: {6,7}
SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__6_7_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__6_7);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__6_7;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 !RefinementVector[6]
 && !RefinementVector[7];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__6_7_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__6_7);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__6_7;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 RefinementVector[6]
 && !RefinementVector[7];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__6_7_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__6_7);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__6_7;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 !RefinementVector[6]
 && RefinementVector[7];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__6_7_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__6_7);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__6_7;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 RefinementVector[6]
 && RefinementVector[7];
endproperty

//SHARounds_to_SHARounds_1_p_sequence
//pair: {7,8}
SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__7_8_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__7_8);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__7_8;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 !RefinementVector[7]
 && !RefinementVector[8];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__7_8_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__7_8);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__7_8;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 RefinementVector[7]
 && !RefinementVector[8];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__7_8_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__7_8);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__7_8;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 !RefinementVector[7]
 && RefinementVector[8];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__7_8_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__7_8);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__7_8;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 RefinementVector[7]
 && RefinementVector[8];
endproperty

//SHARounds_to_SHARounds_1_p_sequence
//pair: {8,9}
SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__8_9_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__8_9);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__8_9;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 !RefinementVector[8]
 && !RefinementVector[9];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__8_9_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__8_9);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__8_9;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 RefinementVector[8]
 && !RefinementVector[9];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__8_9_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__8_9);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__8_9;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 !RefinementVector[8]
 && RefinementVector[9];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__8_9_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__8_9);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__8_9;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 RefinementVector[8]
 && RefinementVector[9];
endproperty

//SHARounds_to_SHARounds_1_p_sequence
//pair: {9,10}
SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__9_10_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__9_10);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__9_10;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 !RefinementVector[9]
 && !RefinementVector[10];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__9_10_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__9_10);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__9_10;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 RefinementVector[9]
 && !RefinementVector[10];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__9_10_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__9_10);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__9_10;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 !RefinementVector[9]
 && RefinementVector[10];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__9_10_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__9_10);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__9_10;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 RefinementVector[9]
 && RefinementVector[10];
endproperty

//SHARounds_to_SHARounds_1_p_sequence
//pair: {10,11}
SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__10_11_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__10_11);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__10_11;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 !RefinementVector[10]
 && !RefinementVector[11];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__10_11_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__10_11);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__10_11;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 RefinementVector[10]
 && !RefinementVector[11];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__10_11_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__10_11);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__10_11;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 !RefinementVector[10]
 && RefinementVector[11];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__10_11_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__10_11);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__10_11;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 RefinementVector[10]
 && RefinementVector[11];
endproperty

//SHARounds_to_SHARounds_1_p_sequence
//pair: {11,12}
SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__11_12_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__11_12);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__11_12;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 !RefinementVector[11]
 && !RefinementVector[12];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__11_12_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__11_12);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__11_12;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 RefinementVector[11]
 && !RefinementVector[12];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__11_12_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__11_12);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__11_12;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 !RefinementVector[11]
 && RefinementVector[12];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__11_12_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__11_12);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__11_12;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 RefinementVector[11]
 && RefinementVector[12];
endproperty

//SHARounds_to_SHARounds_1_p_sequence
//pair: {12,13}
SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__12_13_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__12_13);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__12_13;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 !RefinementVector[12]
 && !RefinementVector[13];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__12_13_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__12_13);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__12_13;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 RefinementVector[12]
 && !RefinementVector[13];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__12_13_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__12_13);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__12_13;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 !RefinementVector[12]
 && RefinementVector[13];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__12_13_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__12_13);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__12_13;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 RefinementVector[12]
 && RefinementVector[13];
endproperty

//SHARounds_to_SHARounds_1_p_sequence
//pair: {13,14}
SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__13_14_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__13_14);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__13_14;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 !RefinementVector[13]
 && !RefinementVector[14];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__13_14_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__13_14);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__13_14;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 RefinementVector[13]
 && !RefinementVector[14];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__13_14_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__13_14);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__13_14;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 !RefinementVector[13]
 && RefinementVector[14];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__13_14_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__13_14);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__13_14;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 RefinementVector[13]
 && RefinementVector[14];
endproperty

//SHARounds_to_SHARounds_1_p_sequence
//pair: {14,15}
SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__14_15_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__14_15);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__14_15;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 !RefinementVector[14]
 && !RefinementVector[15];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__14_15_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__14_15);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__14_15;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 RefinementVector[14]
 && !RefinementVector[15];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__14_15_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__14_15);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__14_15;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 !RefinementVector[14]
 && RefinementVector[15];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__14_15_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__14_15);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__14_15;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 RefinementVector[14]
 && RefinementVector[15];
endproperty

//SHARounds_to_SHARounds_1_p_sequence
//pair: {15,16}
SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__15_16_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__15_16);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__15_16;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 !RefinementVector[15]
 && !RefinementVector[16];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__15_16_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__15_16);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__15_16;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 RefinementVector[15]
 && !RefinementVector[16];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__15_16_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__15_16);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__15_16;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 !RefinementVector[15]
 && RefinementVector[16];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__15_16_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__15_16);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__15_16;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 RefinementVector[15]
 && RefinementVector[16];
endproperty

//SHARounds_to_SHARounds_1_p_sequence
//pair: {16,17}
SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__16_17_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__16_17);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__16_17;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 !RefinementVector[16]
 && !RefinementVector[17];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__16_17_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__16_17);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__16_17;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 RefinementVector[16]
 && !RefinementVector[17];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__16_17_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__16_17);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__16_17;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 !RefinementVector[16]
 && RefinementVector[17];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__16_17_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__16_17);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__16_17;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 RefinementVector[16]
 && RefinementVector[17];
endproperty

//SHARounds_to_SHARounds_1_p_sequence
//pair: {17,18}
SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__17_18_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__17_18);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__17_18;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 !RefinementVector[17]
 && !RefinementVector[18];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__17_18_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__17_18);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__17_18;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 RefinementVector[17]
 && !RefinementVector[18];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__17_18_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__17_18);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__17_18;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 !RefinementVector[17]
 && RefinementVector[18];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__17_18_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__17_18);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__17_18;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 RefinementVector[17]
 && RefinementVector[18];
endproperty

//SHARounds_to_SHARounds_1_p_sequence
//pair: {18,31}
SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__18_31_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__18_31);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__0__18_31;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 !RefinementVector[18]
 && !RefinementVector[31];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__18_31_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__18_31);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__1__18_31;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 RefinementVector[18]
 && !RefinementVector[31];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__18_31_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__18_31);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__2__18_31;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 !RefinementVector[18]
 && RefinementVector[31];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__18_31_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__18_31);
property SHARounds__pairing__SHARounds_to_SHARounds_1_p_sequence__3__18_31;
 SHARounds_to_SHARounds_1_p_sequence
|->
 ##1 RefinementVector[18]
 && RefinementVector[31];
endproperty


//SHARounds_to_SHARounds_p_sequence
//pair: {0,1}
SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__0__0_1_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__0__0_1);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__0__0_1;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 !RefinementVector[0]
 && !RefinementVector[1];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__1__0_1_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__1__0_1);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__1__0_1;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 RefinementVector[0]
 && !RefinementVector[1];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__2__0_1_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__2__0_1);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__2__0_1;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 !RefinementVector[0]
 && RefinementVector[1];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__3__0_1_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__3__0_1);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__3__0_1;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 RefinementVector[0]
 && RefinementVector[1];
endproperty

//SHARounds_to_SHARounds_p_sequence
//pair: {1,2}
SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__0__1_2_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__0__1_2);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__0__1_2;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 !RefinementVector[1]
 && !RefinementVector[2];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__1__1_2_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__1__1_2);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__1__1_2;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 RefinementVector[1]
 && !RefinementVector[2];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__2__1_2_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__2__1_2);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__2__1_2;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 !RefinementVector[1]
 && RefinementVector[2];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__3__1_2_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__3__1_2);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__3__1_2;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 RefinementVector[1]
 && RefinementVector[2];
endproperty

//SHARounds_to_SHARounds_p_sequence
//pair: {2,3}
SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__0__2_3_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__0__2_3);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__0__2_3;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 !RefinementVector[2]
 && !RefinementVector[3];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__1__2_3_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__1__2_3);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__1__2_3;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 RefinementVector[2]
 && !RefinementVector[3];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__2__2_3_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__2__2_3);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__2__2_3;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 !RefinementVector[2]
 && RefinementVector[3];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__3__2_3_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__3__2_3);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__3__2_3;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 RefinementVector[2]
 && RefinementVector[3];
endproperty

//SHARounds_to_SHARounds_p_sequence
//pair: {3,5}
SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__0__3_5_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__0__3_5);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__0__3_5;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 !RefinementVector[3]
 && !RefinementVector[5];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__1__3_5_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__1__3_5);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__1__3_5;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 RefinementVector[3]
 && !RefinementVector[5];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__2__3_5_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__2__3_5);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__2__3_5;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 !RefinementVector[3]
 && RefinementVector[5];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__3__3_5_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__3__3_5);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__3__3_5;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 RefinementVector[3]
 && RefinementVector[5];
endproperty

//SHARounds_to_SHARounds_p_sequence
//pair: {5,6}
SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__0__5_6_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__0__5_6);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__0__5_6;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 !RefinementVector[5]
 && !RefinementVector[6];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__1__5_6_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__1__5_6);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__1__5_6;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 RefinementVector[5]
 && !RefinementVector[6];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__2__5_6_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__2__5_6);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__2__5_6;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 !RefinementVector[5]
 && RefinementVector[6];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__3__5_6_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__3__5_6);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__3__5_6;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 RefinementVector[5]
 && RefinementVector[6];
endproperty

//SHARounds_to_SHARounds_p_sequence
//pair: {6,7}
SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__0__6_7_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__0__6_7);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__0__6_7;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 !RefinementVector[6]
 && !RefinementVector[7];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__1__6_7_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__1__6_7);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__1__6_7;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 RefinementVector[6]
 && !RefinementVector[7];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__2__6_7_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__2__6_7);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__2__6_7;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 !RefinementVector[6]
 && RefinementVector[7];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__3__6_7_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__3__6_7);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__3__6_7;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 RefinementVector[6]
 && RefinementVector[7];
endproperty

//SHARounds_to_SHARounds_p_sequence
//pair: {7,8}
SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__0__7_8_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__0__7_8);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__0__7_8;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 !RefinementVector[7]
 && !RefinementVector[8];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__1__7_8_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__1__7_8);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__1__7_8;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 RefinementVector[7]
 && !RefinementVector[8];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__2__7_8_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__2__7_8);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__2__7_8;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 !RefinementVector[7]
 && RefinementVector[8];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__3__7_8_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__3__7_8);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__3__7_8;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 RefinementVector[7]
 && RefinementVector[8];
endproperty

//SHARounds_to_SHARounds_p_sequence
//pair: {8,9}
SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__0__8_9_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__0__8_9);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__0__8_9;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 !RefinementVector[8]
 && !RefinementVector[9];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__1__8_9_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__1__8_9);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__1__8_9;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 RefinementVector[8]
 && !RefinementVector[9];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__2__8_9_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__2__8_9);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__2__8_9;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 !RefinementVector[8]
 && RefinementVector[9];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__3__8_9_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__3__8_9);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__3__8_9;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 RefinementVector[8]
 && RefinementVector[9];
endproperty

//SHARounds_to_SHARounds_p_sequence
//pair: {9,12}
SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__0__9_12_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__0__9_12);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__0__9_12;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 !RefinementVector[9]
 && !RefinementVector[12];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__1__9_12_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__1__9_12);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__1__9_12;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 RefinementVector[9]
 && !RefinementVector[12];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__2__9_12_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__2__9_12);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__2__9_12;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 !RefinementVector[9]
 && RefinementVector[12];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__3__9_12_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__3__9_12);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__3__9_12;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 RefinementVector[9]
 && RefinementVector[12];
endproperty

//SHARounds_to_SHARounds_p_sequence
//pair: {12,13}
SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__0__12_13_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__0__12_13);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__0__12_13;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 !RefinementVector[12]
 && !RefinementVector[13];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__1__12_13_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__1__12_13);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__1__12_13;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 RefinementVector[12]
 && !RefinementVector[13];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__2__12_13_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__2__12_13);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__2__12_13;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 !RefinementVector[12]
 && RefinementVector[13];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__3__12_13_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__3__12_13);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__3__12_13;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 RefinementVector[12]
 && RefinementVector[13];
endproperty

//SHARounds_to_SHARounds_p_sequence
//pair: {13,14}
SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__0__13_14_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__0__13_14);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__0__13_14;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 !RefinementVector[13]
 && !RefinementVector[14];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__1__13_14_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__1__13_14);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__1__13_14;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 RefinementVector[13]
 && !RefinementVector[14];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__2__13_14_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__2__13_14);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__2__13_14;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 !RefinementVector[13]
 && RefinementVector[14];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__3__13_14_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__3__13_14);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__3__13_14;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 RefinementVector[13]
 && RefinementVector[14];
endproperty

//SHARounds_to_SHARounds_p_sequence
//pair: {14,15}
SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__0__14_15_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__0__14_15);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__0__14_15;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 !RefinementVector[14]
 && !RefinementVector[15];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__1__14_15_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__1__14_15);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__1__14_15;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 RefinementVector[14]
 && !RefinementVector[15];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__2__14_15_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__2__14_15);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__2__14_15;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 !RefinementVector[14]
 && RefinementVector[15];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__3__14_15_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__3__14_15);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__3__14_15;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 RefinementVector[14]
 && RefinementVector[15];
endproperty

//SHARounds_to_SHARounds_p_sequence
//pair: {15,16}
SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__0__15_16_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__0__15_16);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__0__15_16;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 !RefinementVector[15]
 && !RefinementVector[16];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__1__15_16_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__1__15_16);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__1__15_16;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 RefinementVector[15]
 && !RefinementVector[16];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__2__15_16_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__2__15_16);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__2__15_16;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 !RefinementVector[15]
 && RefinementVector[16];
endproperty

SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__3__15_16_a: assert property (disable iff(reset_n || zeroize) SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__3__15_16);
property SHARounds__pairing__SHARounds_to_SHARounds_p_sequence__3__15_16;
 SHARounds_to_SHARounds_p_sequence
|->
 ##1 RefinementVector[15]
 && RefinementVector[16];
endproperty


/*************************************/
/* DONE state bit-pairing properties */
/*************************************/

//SHARounds_to_DONE_p_sequence
//pair: {0,1}
DONE__pairing__SHARounds_to_DONE_p_sequence__0__0_1_a: assert property (disable iff(reset_n || zeroize) DONE__pairing__SHARounds_to_DONE_p_sequence__0__0_1);
property DONE__pairing__SHARounds_to_DONE_p_sequence__0__0_1;
 SHARounds_to_DONE_p_sequence
|->
 ##1 !RefinementVector[0]
 && !RefinementVector[1];
endproperty

DONE__pairing__SHARounds_to_DONE_p_sequence__1__0_1_a: assert property (disable iff(reset_n || zeroize) DONE__pairing__SHARounds_to_DONE_p_sequence__1__0_1);
property DONE__pairing__SHARounds_to_DONE_p_sequence__1__0_1;
 SHARounds_to_DONE_p_sequence
|->
 ##1 RefinementVector[0]
 && !RefinementVector[1];
endproperty

DONE__pairing__SHARounds_to_DONE_p_sequence__2__0_1_a: assert property (disable iff(reset_n || zeroize) DONE__pairing__SHARounds_to_DONE_p_sequence__2__0_1);
property DONE__pairing__SHARounds_to_DONE_p_sequence__2__0_1;
 SHARounds_to_DONE_p_sequence
|->
 ##1 !RefinementVector[0]
 && RefinementVector[1];
endproperty

DONE__pairing__SHARounds_to_DONE_p_sequence__3__0_1_a: assert property (disable iff(reset_n || zeroize) DONE__pairing__SHARounds_to_DONE_p_sequence__3__0_1);
property DONE__pairing__SHARounds_to_DONE_p_sequence__3__0_1;
 SHARounds_to_DONE_p_sequence
|->
 ##1 RefinementVector[0]
 && RefinementVector[1];
endproperty

//SHARounds_to_DONE_p_sequence
//pair: {1,2}
DONE__pairing__SHARounds_to_DONE_p_sequence__0__1_2_a: assert property (disable iff(reset_n || zeroize) DONE__pairing__SHARounds_to_DONE_p_sequence__0__1_2);
property DONE__pairing__SHARounds_to_DONE_p_sequence__0__1_2;
 SHARounds_to_DONE_p_sequence
|->
 ##1 !RefinementVector[1]
 && !RefinementVector[2];
endproperty

DONE__pairing__SHARounds_to_DONE_p_sequence__1__1_2_a: assert property (disable iff(reset_n || zeroize) DONE__pairing__SHARounds_to_DONE_p_sequence__1__1_2);
property DONE__pairing__SHARounds_to_DONE_p_sequence__1__1_2;
 SHARounds_to_DONE_p_sequence
|->
 ##1 RefinementVector[1]
 && !RefinementVector[2];
endproperty

DONE__pairing__SHARounds_to_DONE_p_sequence__2__1_2_a: assert property (disable iff(reset_n || zeroize) DONE__pairing__SHARounds_to_DONE_p_sequence__2__1_2);
property DONE__pairing__SHARounds_to_DONE_p_sequence__2__1_2;
 SHARounds_to_DONE_p_sequence
|->
 ##1 !RefinementVector[1]
 && RefinementVector[2];
endproperty

DONE__pairing__SHARounds_to_DONE_p_sequence__3__1_2_a: assert property (disable iff(reset_n || zeroize) DONE__pairing__SHARounds_to_DONE_p_sequence__3__1_2);
property DONE__pairing__SHARounds_to_DONE_p_sequence__3__1_2;
 SHARounds_to_DONE_p_sequence
|->
 ##1 RefinementVector[1]
 && RefinementVector[2];
endproperty

//SHARounds_to_DONE_p_sequence
//pair: {2,3}
DONE__pairing__SHARounds_to_DONE_p_sequence__0__2_3_a: assert property (disable iff(reset_n || zeroize) DONE__pairing__SHARounds_to_DONE_p_sequence__0__2_3);
property DONE__pairing__SHARounds_to_DONE_p_sequence__0__2_3;
 SHARounds_to_DONE_p_sequence
|->
 ##1 !RefinementVector[2]
 && !RefinementVector[3];
endproperty

DONE__pairing__SHARounds_to_DONE_p_sequence__1__2_3_a: assert property (disable iff(reset_n || zeroize) DONE__pairing__SHARounds_to_DONE_p_sequence__1__2_3);
property DONE__pairing__SHARounds_to_DONE_p_sequence__1__2_3;
 SHARounds_to_DONE_p_sequence
|->
 ##1 RefinementVector[2]
 && !RefinementVector[3];
endproperty

DONE__pairing__SHARounds_to_DONE_p_sequence__2__2_3_a: assert property (disable iff(reset_n || zeroize) DONE__pairing__SHARounds_to_DONE_p_sequence__2__2_3);
property DONE__pairing__SHARounds_to_DONE_p_sequence__2__2_3;
 SHARounds_to_DONE_p_sequence
|->
 ##1 !RefinementVector[2]
 && RefinementVector[3];
endproperty

DONE__pairing__SHARounds_to_DONE_p_sequence__3__2_3_a: assert property (disable iff(reset_n || zeroize) DONE__pairing__SHARounds_to_DONE_p_sequence__3__2_3);
property DONE__pairing__SHARounds_to_DONE_p_sequence__3__2_3;
 SHARounds_to_DONE_p_sequence
|->
 ##1 RefinementVector[2]
 && RefinementVector[3];
endproperty



endmodule
