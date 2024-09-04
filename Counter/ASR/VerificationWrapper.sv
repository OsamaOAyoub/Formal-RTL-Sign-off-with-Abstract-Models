`include "counter.sv"
`include "cntr.sv"
`include "cntr_computational.sv"
`include "cntr_control.sv"
`include "cntr_operations.sv"
`include "global_package.sv"

//Wrapper definition
module VerificationWrapper #(
    parameter N = 7
)(
  input logic clk,
  input logic rst,
  input logic en,
  output logic [N-1:0] cnt
);

//DUT instantiation
counter dut_inst (
  .clk(clk),
  .rst(rst),
  .en(en),
  .cnt(cnt)
);


//Generated RTL instantiation
cntr cntr (
  .rst(rst),
  .clk(clk),
  .cnt_out_sig(),
  .en_sig(en)
);

default clocking default_clk @(posedge clk); endclocking

sequence reset_sequence;
  rst ##1 !rst;
endsequence

sequence reset_p_sequence;
  reset_sequence;
endsequence

sequence state_to_state_p_sequence;
  (cntr.cntr_control_inst.current_state==0) &&
  cntr.en_sig &&
  (cntr.cntr_computational_inst.cnt_out_t == 127);
endsequence

sequence state_to_state_1_p_sequence;
  (cntr.cntr_control_inst.current_state==0) &&
  cntr.en_sig &&
  (cntr.cntr_computational_inst.cnt_out_t != 127);
endsequence

sequence state_to_state_2_p_sequence;
  (cntr.cntr_control_inst.current_state==0) &&
  !cntr.en_sig;
endsequence

//Smart states refiner properties

//RefinementVector binding
logic [9:0] RefinementVector;
assign RefinementVector[0] = dut_inst.en;
assign RefinementVector[7:1] = dut_inst.cnt;
assign RefinementVector[8] = dut_inst.en_1;
assign RefinementVector[9] = dut_inst.en_2;


//Bit blasting properties

/***************************************/
/* state state bit-blasting properties */
/***************************************/

//state_to_state_p_sequence
for(genvar bitNum = 0; bitNum < 10 ; bitNum++) begin: state__blasting__state_to_state_p_sequence_gen
 state__blasting__state_to_state_p_sequence_a: assert property (disable iff(rst)state__blasting__state_to_state_p_sequence(bitNum));
 state__blasting__state_to_state_p_sequence_NOT_a: assert property (disable iff(rst)state__blasting__state_to_state_p_sequence_NOT(bitNum));
end

property state__blasting__state_to_state_p_sequence(bitPos);
 state_to_state_p_sequence
|->
 ##1 RefinementVector[bitPos];
endproperty

property state__blasting__state_to_state_p_sequence_NOT(bitPos);
 state_to_state_p_sequence
|->
 ##1 !RefinementVector[bitPos];
endproperty

//state_to_state_1_p_sequence
for(genvar bitNum = 0; bitNum < 10 ; bitNum++) begin: state__blasting__state_to_state_1_p_sequence_gen
 state__blasting__state_to_state_1_p_sequence_a: assert property (disable iff(rst)state__blasting__state_to_state_1_p_sequence(bitNum));
 state__blasting__state_to_state_1_p_sequence_NOT_a: assert property (disable iff(rst)state__blasting__state_to_state_1_p_sequence_NOT(bitNum));
end

property state__blasting__state_to_state_1_p_sequence(bitPos);
 state_to_state_1_p_sequence
|->
 ##1 RefinementVector[bitPos];
endproperty

property state__blasting__state_to_state_1_p_sequence_NOT(bitPos);
 state_to_state_1_p_sequence
|->
 ##1 !RefinementVector[bitPos];
endproperty

//state_to_state_2_p_sequence
for(genvar bitNum = 0; bitNum < 10 ; bitNum++) begin: state__blasting__state_to_state_2_p_sequence_gen
 state__blasting__state_to_state_2_p_sequence_a: assert property (disable iff(rst)state__blasting__state_to_state_2_p_sequence(bitNum));
 state__blasting__state_to_state_2_p_sequence_NOT_a: assert property (disable iff(rst)state__blasting__state_to_state_2_p_sequence_NOT(bitNum));
end

property state__blasting__state_to_state_2_p_sequence(bitPos);
 state_to_state_2_p_sequence
|->
 ##1 RefinementVector[bitPos];
endproperty

property state__blasting__state_to_state_2_p_sequence_NOT(bitPos);
 state_to_state_2_p_sequence
|->
 ##1 !RefinementVector[bitPos];
endproperty

//reset_p_sequence
for(genvar bitNum = 0; bitNum < 10 ; bitNum++) begin: state__blasting__reset_p_sequence_gen
 state__blasting__reset_p_sequence_a: assert property (state__blasting__reset_p_sequence(bitNum));
 state__blasting__reset_p_sequence_NOT_a: assert property (state__blasting__reset_p_sequence_NOT(bitNum));
end

property state__blasting__reset_p_sequence(bitPos);
 reset_p_sequence
|->
 RefinementVector[bitPos];
endproperty

property state__blasting__reset_p_sequence_NOT(bitPos);
 reset_p_sequence
|->
 !RefinementVector[bitPos];
endproperty


//Bit pairing properties

/**************************************/
/* state state bit-pairing properties */
/**************************************/


//state_to_state_1_p_sequence
//pair: {0,1}
state__pairing__state_to_state_1_p_sequence__0__0_1_a: assert property (disable iff(rst) state__pairing__state_to_state_1_p_sequence__0__0_1);
property state__pairing__state_to_state_1_p_sequence__0__0_1;
 state_to_state_1_p_sequence
|->
 ##1 !RefinementVector[0]
 && !RefinementVector[1];
endproperty

state__pairing__state_to_state_1_p_sequence__1__0_1_a: assert property (disable iff(rst) state__pairing__state_to_state_1_p_sequence__1__0_1);
property state__pairing__state_to_state_1_p_sequence__1__0_1;
 state_to_state_1_p_sequence
|->
 ##1 RefinementVector[0]
 && !RefinementVector[1];
endproperty

state__pairing__state_to_state_1_p_sequence__2__0_1_a: assert property (disable iff(rst) state__pairing__state_to_state_1_p_sequence__2__0_1);
property state__pairing__state_to_state_1_p_sequence__2__0_1;
 state_to_state_1_p_sequence
|->
 ##1 !RefinementVector[0]
 && RefinementVector[1];
endproperty

state__pairing__state_to_state_1_p_sequence__3__0_1_a: assert property (disable iff(rst) state__pairing__state_to_state_1_p_sequence__3__0_1);
property state__pairing__state_to_state_1_p_sequence__3__0_1;
 state_to_state_1_p_sequence
|->
 ##1 RefinementVector[0]
 && RefinementVector[1];
endproperty

//state_to_state_1_p_sequence
//pair: {1,2}
state__pairing__state_to_state_1_p_sequence__0__1_2_a: assert property (disable iff(rst) state__pairing__state_to_state_1_p_sequence__0__1_2);
property state__pairing__state_to_state_1_p_sequence__0__1_2;
 state_to_state_1_p_sequence
|->
 ##1 !RefinementVector[1]
 && !RefinementVector[2];
endproperty

state__pairing__state_to_state_1_p_sequence__1__1_2_a: assert property (disable iff(rst) state__pairing__state_to_state_1_p_sequence__1__1_2);
property state__pairing__state_to_state_1_p_sequence__1__1_2;
 state_to_state_1_p_sequence
|->
 ##1 RefinementVector[1]
 && !RefinementVector[2];
endproperty

state__pairing__state_to_state_1_p_sequence__2__1_2_a: assert property (disable iff(rst) state__pairing__state_to_state_1_p_sequence__2__1_2);
property state__pairing__state_to_state_1_p_sequence__2__1_2;
 state_to_state_1_p_sequence
|->
 ##1 !RefinementVector[1]
 && RefinementVector[2];
endproperty

state__pairing__state_to_state_1_p_sequence__3__1_2_a: assert property (disable iff(rst) state__pairing__state_to_state_1_p_sequence__3__1_2);
property state__pairing__state_to_state_1_p_sequence__3__1_2;
 state_to_state_1_p_sequence
|->
 ##1 RefinementVector[1]
 && RefinementVector[2];
endproperty

//state_to_state_1_p_sequence
//pair: {2,3}
state__pairing__state_to_state_1_p_sequence__0__2_3_a: assert property (disable iff(rst) state__pairing__state_to_state_1_p_sequence__0__2_3);
property state__pairing__state_to_state_1_p_sequence__0__2_3;
 state_to_state_1_p_sequence
|->
 ##1 !RefinementVector[2]
 && !RefinementVector[3];
endproperty

state__pairing__state_to_state_1_p_sequence__1__2_3_a: assert property (disable iff(rst) state__pairing__state_to_state_1_p_sequence__1__2_3);
property state__pairing__state_to_state_1_p_sequence__1__2_3;
 state_to_state_1_p_sequence
|->
 ##1 RefinementVector[2]
 && !RefinementVector[3];
endproperty

state__pairing__state_to_state_1_p_sequence__2__2_3_a: assert property (disable iff(rst) state__pairing__state_to_state_1_p_sequence__2__2_3);
property state__pairing__state_to_state_1_p_sequence__2__2_3;
 state_to_state_1_p_sequence
|->
 ##1 !RefinementVector[2]
 && RefinementVector[3];
endproperty

state__pairing__state_to_state_1_p_sequence__3__2_3_a: assert property (disable iff(rst) state__pairing__state_to_state_1_p_sequence__3__2_3);
property state__pairing__state_to_state_1_p_sequence__3__2_3;
 state_to_state_1_p_sequence
|->
 ##1 RefinementVector[2]
 && RefinementVector[3];
endproperty

//state_to_state_1_p_sequence
//pair: {3,4}
state__pairing__state_to_state_1_p_sequence__0__3_4_a: assert property (disable iff(rst) state__pairing__state_to_state_1_p_sequence__0__3_4);
property state__pairing__state_to_state_1_p_sequence__0__3_4;
 state_to_state_1_p_sequence
|->
 ##1 !RefinementVector[3]
 && !RefinementVector[4];
endproperty

state__pairing__state_to_state_1_p_sequence__1__3_4_a: assert property (disable iff(rst) state__pairing__state_to_state_1_p_sequence__1__3_4);
property state__pairing__state_to_state_1_p_sequence__1__3_4;
 state_to_state_1_p_sequence
|->
 ##1 RefinementVector[3]
 && !RefinementVector[4];
endproperty

state__pairing__state_to_state_1_p_sequence__2__3_4_a: assert property (disable iff(rst) state__pairing__state_to_state_1_p_sequence__2__3_4);
property state__pairing__state_to_state_1_p_sequence__2__3_4;
 state_to_state_1_p_sequence
|->
 ##1 !RefinementVector[3]
 && RefinementVector[4];
endproperty

state__pairing__state_to_state_1_p_sequence__3__3_4_a: assert property (disable iff(rst) state__pairing__state_to_state_1_p_sequence__3__3_4);
property state__pairing__state_to_state_1_p_sequence__3__3_4;
 state_to_state_1_p_sequence
|->
 ##1 RefinementVector[3]
 && RefinementVector[4];
endproperty

//state_to_state_1_p_sequence
//pair: {4,5}
state__pairing__state_to_state_1_p_sequence__0__4_5_a: assert property (disable iff(rst) state__pairing__state_to_state_1_p_sequence__0__4_5);
property state__pairing__state_to_state_1_p_sequence__0__4_5;
 state_to_state_1_p_sequence
|->
 ##1 !RefinementVector[4]
 && !RefinementVector[5];
endproperty

state__pairing__state_to_state_1_p_sequence__1__4_5_a: assert property (disable iff(rst) state__pairing__state_to_state_1_p_sequence__1__4_5);
property state__pairing__state_to_state_1_p_sequence__1__4_5;
 state_to_state_1_p_sequence
|->
 ##1 RefinementVector[4]
 && !RefinementVector[5];
endproperty

state__pairing__state_to_state_1_p_sequence__2__4_5_a: assert property (disable iff(rst) state__pairing__state_to_state_1_p_sequence__2__4_5);
property state__pairing__state_to_state_1_p_sequence__2__4_5;
 state_to_state_1_p_sequence
|->
 ##1 !RefinementVector[4]
 && RefinementVector[5];
endproperty

state__pairing__state_to_state_1_p_sequence__3__4_5_a: assert property (disable iff(rst) state__pairing__state_to_state_1_p_sequence__3__4_5);
property state__pairing__state_to_state_1_p_sequence__3__4_5;
 state_to_state_1_p_sequence
|->
 ##1 RefinementVector[4]
 && RefinementVector[5];
endproperty

//state_to_state_1_p_sequence
//pair: {5,6}
state__pairing__state_to_state_1_p_sequence__0__5_6_a: assert property (disable iff(rst) state__pairing__state_to_state_1_p_sequence__0__5_6);
property state__pairing__state_to_state_1_p_sequence__0__5_6;
 state_to_state_1_p_sequence
|->
 ##1 !RefinementVector[5]
 && !RefinementVector[6];
endproperty

state__pairing__state_to_state_1_p_sequence__1__5_6_a: assert property (disable iff(rst) state__pairing__state_to_state_1_p_sequence__1__5_6);
property state__pairing__state_to_state_1_p_sequence__1__5_6;
 state_to_state_1_p_sequence
|->
 ##1 RefinementVector[5]
 && !RefinementVector[6];
endproperty

state__pairing__state_to_state_1_p_sequence__2__5_6_a: assert property (disable iff(rst) state__pairing__state_to_state_1_p_sequence__2__5_6);
property state__pairing__state_to_state_1_p_sequence__2__5_6;
 state_to_state_1_p_sequence
|->
 ##1 !RefinementVector[5]
 && RefinementVector[6];
endproperty

state__pairing__state_to_state_1_p_sequence__3__5_6_a: assert property (disable iff(rst) state__pairing__state_to_state_1_p_sequence__3__5_6);
property state__pairing__state_to_state_1_p_sequence__3__5_6;
 state_to_state_1_p_sequence
|->
 ##1 RefinementVector[5]
 && RefinementVector[6];
endproperty

//state_to_state_1_p_sequence
//pair: {6,7}
state__pairing__state_to_state_1_p_sequence__0__6_7_a: assert property (disable iff(rst) state__pairing__state_to_state_1_p_sequence__0__6_7);
property state__pairing__state_to_state_1_p_sequence__0__6_7;
 state_to_state_1_p_sequence
|->
 ##1 !RefinementVector[6]
 && !RefinementVector[7];
endproperty

state__pairing__state_to_state_1_p_sequence__1__6_7_a: assert property (disable iff(rst) state__pairing__state_to_state_1_p_sequence__1__6_7);
property state__pairing__state_to_state_1_p_sequence__1__6_7;
 state_to_state_1_p_sequence
|->
 ##1 RefinementVector[6]
 && !RefinementVector[7];
endproperty

state__pairing__state_to_state_1_p_sequence__2__6_7_a: assert property (disable iff(rst) state__pairing__state_to_state_1_p_sequence__2__6_7);
property state__pairing__state_to_state_1_p_sequence__2__6_7;
 state_to_state_1_p_sequence
|->
 ##1 !RefinementVector[6]
 && RefinementVector[7];
endproperty

state__pairing__state_to_state_1_p_sequence__3__6_7_a: assert property (disable iff(rst) state__pairing__state_to_state_1_p_sequence__3__6_7);
property state__pairing__state_to_state_1_p_sequence__3__6_7;
 state_to_state_1_p_sequence
|->
 ##1 RefinementVector[6]
 && RefinementVector[7];
endproperty

//state_to_state_1_p_sequence
//pair: {7,9}
state__pairing__state_to_state_1_p_sequence__0__7_9_a: assert property (disable iff(rst) state__pairing__state_to_state_1_p_sequence__0__7_9);
property state__pairing__state_to_state_1_p_sequence__0__7_9;
 state_to_state_1_p_sequence
|->
 ##1 !RefinementVector[7]
 && !RefinementVector[9];
endproperty

state__pairing__state_to_state_1_p_sequence__1__7_9_a: assert property (disable iff(rst) state__pairing__state_to_state_1_p_sequence__1__7_9);
property state__pairing__state_to_state_1_p_sequence__1__7_9;
 state_to_state_1_p_sequence
|->
 ##1 RefinementVector[7]
 && !RefinementVector[9];
endproperty

state__pairing__state_to_state_1_p_sequence__2__7_9_a: assert property (disable iff(rst) state__pairing__state_to_state_1_p_sequence__2__7_9);
property state__pairing__state_to_state_1_p_sequence__2__7_9;
 state_to_state_1_p_sequence
|->
 ##1 !RefinementVector[7]
 && RefinementVector[9];
endproperty

state__pairing__state_to_state_1_p_sequence__3__7_9_a: assert property (disable iff(rst) state__pairing__state_to_state_1_p_sequence__3__7_9);
property state__pairing__state_to_state_1_p_sequence__3__7_9;
 state_to_state_1_p_sequence
|->
 ##1 RefinementVector[7]
 && RefinementVector[9];
endproperty


//state_to_state_2_p_sequence
//pair: {0,1}
state__pairing__state_to_state_2_p_sequence__0__0_1_a: assert property (disable iff(rst) state__pairing__state_to_state_2_p_sequence__0__0_1);
property state__pairing__state_to_state_2_p_sequence__0__0_1;
 state_to_state_2_p_sequence
|->
 ##1 !RefinementVector[0]
 && !RefinementVector[1];
endproperty

state__pairing__state_to_state_2_p_sequence__1__0_1_a: assert property (disable iff(rst) state__pairing__state_to_state_2_p_sequence__1__0_1);
property state__pairing__state_to_state_2_p_sequence__1__0_1;
 state_to_state_2_p_sequence
|->
 ##1 RefinementVector[0]
 && !RefinementVector[1];
endproperty

state__pairing__state_to_state_2_p_sequence__2__0_1_a: assert property (disable iff(rst) state__pairing__state_to_state_2_p_sequence__2__0_1);
property state__pairing__state_to_state_2_p_sequence__2__0_1;
 state_to_state_2_p_sequence
|->
 ##1 !RefinementVector[0]
 && RefinementVector[1];
endproperty

state__pairing__state_to_state_2_p_sequence__3__0_1_a: assert property (disable iff(rst) state__pairing__state_to_state_2_p_sequence__3__0_1);
property state__pairing__state_to_state_2_p_sequence__3__0_1;
 state_to_state_2_p_sequence
|->
 ##1 RefinementVector[0]
 && RefinementVector[1];
endproperty

//state_to_state_2_p_sequence
//pair: {1,2}
state__pairing__state_to_state_2_p_sequence__0__1_2_a: assert property (disable iff(rst) state__pairing__state_to_state_2_p_sequence__0__1_2);
property state__pairing__state_to_state_2_p_sequence__0__1_2;
 state_to_state_2_p_sequence
|->
 ##1 !RefinementVector[1]
 && !RefinementVector[2];
endproperty

state__pairing__state_to_state_2_p_sequence__1__1_2_a: assert property (disable iff(rst) state__pairing__state_to_state_2_p_sequence__1__1_2);
property state__pairing__state_to_state_2_p_sequence__1__1_2;
 state_to_state_2_p_sequence
|->
 ##1 RefinementVector[1]
 && !RefinementVector[2];
endproperty

state__pairing__state_to_state_2_p_sequence__2__1_2_a: assert property (disable iff(rst) state__pairing__state_to_state_2_p_sequence__2__1_2);
property state__pairing__state_to_state_2_p_sequence__2__1_2;
 state_to_state_2_p_sequence
|->
 ##1 !RefinementVector[1]
 && RefinementVector[2];
endproperty

state__pairing__state_to_state_2_p_sequence__3__1_2_a: assert property (disable iff(rst) state__pairing__state_to_state_2_p_sequence__3__1_2);
property state__pairing__state_to_state_2_p_sequence__3__1_2;
 state_to_state_2_p_sequence
|->
 ##1 RefinementVector[1]
 && RefinementVector[2];
endproperty

//state_to_state_2_p_sequence
//pair: {2,3}
state__pairing__state_to_state_2_p_sequence__0__2_3_a: assert property (disable iff(rst) state__pairing__state_to_state_2_p_sequence__0__2_3);
property state__pairing__state_to_state_2_p_sequence__0__2_3;
 state_to_state_2_p_sequence
|->
 ##1 !RefinementVector[2]
 && !RefinementVector[3];
endproperty

state__pairing__state_to_state_2_p_sequence__1__2_3_a: assert property (disable iff(rst) state__pairing__state_to_state_2_p_sequence__1__2_3);
property state__pairing__state_to_state_2_p_sequence__1__2_3;
 state_to_state_2_p_sequence
|->
 ##1 RefinementVector[2]
 && !RefinementVector[3];
endproperty

state__pairing__state_to_state_2_p_sequence__2__2_3_a: assert property (disable iff(rst) state__pairing__state_to_state_2_p_sequence__2__2_3);
property state__pairing__state_to_state_2_p_sequence__2__2_3;
 state_to_state_2_p_sequence
|->
 ##1 !RefinementVector[2]
 && RefinementVector[3];
endproperty

state__pairing__state_to_state_2_p_sequence__3__2_3_a: assert property (disable iff(rst) state__pairing__state_to_state_2_p_sequence__3__2_3);
property state__pairing__state_to_state_2_p_sequence__3__2_3;
 state_to_state_2_p_sequence
|->
 ##1 RefinementVector[2]
 && RefinementVector[3];
endproperty

//state_to_state_2_p_sequence
//pair: {3,4}
state__pairing__state_to_state_2_p_sequence__0__3_4_a: assert property (disable iff(rst) state__pairing__state_to_state_2_p_sequence__0__3_4);
property state__pairing__state_to_state_2_p_sequence__0__3_4;
 state_to_state_2_p_sequence
|->
 ##1 !RefinementVector[3]
 && !RefinementVector[4];
endproperty

state__pairing__state_to_state_2_p_sequence__1__3_4_a: assert property (disable iff(rst) state__pairing__state_to_state_2_p_sequence__1__3_4);
property state__pairing__state_to_state_2_p_sequence__1__3_4;
 state_to_state_2_p_sequence
|->
 ##1 RefinementVector[3]
 && !RefinementVector[4];
endproperty

state__pairing__state_to_state_2_p_sequence__2__3_4_a: assert property (disable iff(rst) state__pairing__state_to_state_2_p_sequence__2__3_4);
property state__pairing__state_to_state_2_p_sequence__2__3_4;
 state_to_state_2_p_sequence
|->
 ##1 !RefinementVector[3]
 && RefinementVector[4];
endproperty

state__pairing__state_to_state_2_p_sequence__3__3_4_a: assert property (disable iff(rst) state__pairing__state_to_state_2_p_sequence__3__3_4);
property state__pairing__state_to_state_2_p_sequence__3__3_4;
 state_to_state_2_p_sequence
|->
 ##1 RefinementVector[3]
 && RefinementVector[4];
endproperty

//state_to_state_2_p_sequence
//pair: {4,5}
state__pairing__state_to_state_2_p_sequence__0__4_5_a: assert property (disable iff(rst) state__pairing__state_to_state_2_p_sequence__0__4_5);
property state__pairing__state_to_state_2_p_sequence__0__4_5;
 state_to_state_2_p_sequence
|->
 ##1 !RefinementVector[4]
 && !RefinementVector[5];
endproperty

state__pairing__state_to_state_2_p_sequence__1__4_5_a: assert property (disable iff(rst) state__pairing__state_to_state_2_p_sequence__1__4_5);
property state__pairing__state_to_state_2_p_sequence__1__4_5;
 state_to_state_2_p_sequence
|->
 ##1 RefinementVector[4]
 && !RefinementVector[5];
endproperty

state__pairing__state_to_state_2_p_sequence__2__4_5_a: assert property (disable iff(rst) state__pairing__state_to_state_2_p_sequence__2__4_5);
property state__pairing__state_to_state_2_p_sequence__2__4_5;
 state_to_state_2_p_sequence
|->
 ##1 !RefinementVector[4]
 && RefinementVector[5];
endproperty

state__pairing__state_to_state_2_p_sequence__3__4_5_a: assert property (disable iff(rst) state__pairing__state_to_state_2_p_sequence__3__4_5);
property state__pairing__state_to_state_2_p_sequence__3__4_5;
 state_to_state_2_p_sequence
|->
 ##1 RefinementVector[4]
 && RefinementVector[5];
endproperty

//state_to_state_2_p_sequence
//pair: {5,6}
state__pairing__state_to_state_2_p_sequence__0__5_6_a: assert property (disable iff(rst) state__pairing__state_to_state_2_p_sequence__0__5_6);
property state__pairing__state_to_state_2_p_sequence__0__5_6;
 state_to_state_2_p_sequence
|->
 ##1 !RefinementVector[5]
 && !RefinementVector[6];
endproperty

state__pairing__state_to_state_2_p_sequence__1__5_6_a: assert property (disable iff(rst) state__pairing__state_to_state_2_p_sequence__1__5_6);
property state__pairing__state_to_state_2_p_sequence__1__5_6;
 state_to_state_2_p_sequence
|->
 ##1 RefinementVector[5]
 && !RefinementVector[6];
endproperty

state__pairing__state_to_state_2_p_sequence__2__5_6_a: assert property (disable iff(rst) state__pairing__state_to_state_2_p_sequence__2__5_6);
property state__pairing__state_to_state_2_p_sequence__2__5_6;
 state_to_state_2_p_sequence
|->
 ##1 !RefinementVector[5]
 && RefinementVector[6];
endproperty

state__pairing__state_to_state_2_p_sequence__3__5_6_a: assert property (disable iff(rst) state__pairing__state_to_state_2_p_sequence__3__5_6);
property state__pairing__state_to_state_2_p_sequence__3__5_6;
 state_to_state_2_p_sequence
|->
 ##1 RefinementVector[5]
 && RefinementVector[6];
endproperty

//state_to_state_2_p_sequence
//pair: {6,7}
state__pairing__state_to_state_2_p_sequence__0__6_7_a: assert property (disable iff(rst) state__pairing__state_to_state_2_p_sequence__0__6_7);
property state__pairing__state_to_state_2_p_sequence__0__6_7;
 state_to_state_2_p_sequence
|->
 ##1 !RefinementVector[6]
 && !RefinementVector[7];
endproperty

state__pairing__state_to_state_2_p_sequence__1__6_7_a: assert property (disable iff(rst) state__pairing__state_to_state_2_p_sequence__1__6_7);
property state__pairing__state_to_state_2_p_sequence__1__6_7;
 state_to_state_2_p_sequence
|->
 ##1 RefinementVector[6]
 && !RefinementVector[7];
endproperty

state__pairing__state_to_state_2_p_sequence__2__6_7_a: assert property (disable iff(rst) state__pairing__state_to_state_2_p_sequence__2__6_7);
property state__pairing__state_to_state_2_p_sequence__2__6_7;
 state_to_state_2_p_sequence
|->
 ##1 !RefinementVector[6]
 && RefinementVector[7];
endproperty

state__pairing__state_to_state_2_p_sequence__3__6_7_a: assert property (disable iff(rst) state__pairing__state_to_state_2_p_sequence__3__6_7);
property state__pairing__state_to_state_2_p_sequence__3__6_7;
 state_to_state_2_p_sequence
|->
 ##1 RefinementVector[6]
 && RefinementVector[7];
endproperty

//state_to_state_2_p_sequence
//pair: {7,9}
state__pairing__state_to_state_2_p_sequence__0__7_9_a: assert property (disable iff(rst) state__pairing__state_to_state_2_p_sequence__0__7_9);
property state__pairing__state_to_state_2_p_sequence__0__7_9;
 state_to_state_2_p_sequence
|->
 ##1 !RefinementVector[7]
 && !RefinementVector[9];
endproperty

state__pairing__state_to_state_2_p_sequence__1__7_9_a: assert property (disable iff(rst) state__pairing__state_to_state_2_p_sequence__1__7_9);
property state__pairing__state_to_state_2_p_sequence__1__7_9;
 state_to_state_2_p_sequence
|->
 ##1 RefinementVector[7]
 && !RefinementVector[9];
endproperty

state__pairing__state_to_state_2_p_sequence__2__7_9_a: assert property (disable iff(rst) state__pairing__state_to_state_2_p_sequence__2__7_9);
property state__pairing__state_to_state_2_p_sequence__2__7_9;
 state_to_state_2_p_sequence
|->
 ##1 !RefinementVector[7]
 && RefinementVector[9];
endproperty

state__pairing__state_to_state_2_p_sequence__3__7_9_a: assert property (disable iff(rst) state__pairing__state_to_state_2_p_sequence__3__7_9);
property state__pairing__state_to_state_2_p_sequence__3__7_9;
 state_to_state_2_p_sequence
|->
 ##1 RefinementVector[7]
 && RefinementVector[9];
endproperty


//state_to_state_p_sequence
//pair: {0,1}
state__pairing__state_to_state_p_sequence__0__0_1_a: assert property (disable iff(rst) state__pairing__state_to_state_p_sequence__0__0_1);
property state__pairing__state_to_state_p_sequence__0__0_1;
 state_to_state_p_sequence
|->
 ##1 !RefinementVector[0]
 && !RefinementVector[1];
endproperty

state__pairing__state_to_state_p_sequence__1__0_1_a: assert property (disable iff(rst) state__pairing__state_to_state_p_sequence__1__0_1);
property state__pairing__state_to_state_p_sequence__1__0_1;
 state_to_state_p_sequence
|->
 ##1 RefinementVector[0]
 && !RefinementVector[1];
endproperty

state__pairing__state_to_state_p_sequence__2__0_1_a: assert property (disable iff(rst) state__pairing__state_to_state_p_sequence__2__0_1);
property state__pairing__state_to_state_p_sequence__2__0_1;
 state_to_state_p_sequence
|->
 ##1 !RefinementVector[0]
 && RefinementVector[1];
endproperty

state__pairing__state_to_state_p_sequence__3__0_1_a: assert property (disable iff(rst) state__pairing__state_to_state_p_sequence__3__0_1);
property state__pairing__state_to_state_p_sequence__3__0_1;
 state_to_state_p_sequence
|->
 ##1 RefinementVector[0]
 && RefinementVector[1];
endproperty

//state_to_state_p_sequence
//pair: {1,9}
state__pairing__state_to_state_p_sequence__0__1_9_a: assert property (disable iff(rst) state__pairing__state_to_state_p_sequence__0__1_9);
property state__pairing__state_to_state_p_sequence__0__1_9;
 state_to_state_p_sequence
|->
 ##1 !RefinementVector[1]
 && !RefinementVector[9];
endproperty

state__pairing__state_to_state_p_sequence__1__1_9_a: assert property (disable iff(rst) state__pairing__state_to_state_p_sequence__1__1_9);
property state__pairing__state_to_state_p_sequence__1__1_9;
 state_to_state_p_sequence
|->
 ##1 RefinementVector[1]
 && !RefinementVector[9];
endproperty

state__pairing__state_to_state_p_sequence__2__1_9_a: assert property (disable iff(rst) state__pairing__state_to_state_p_sequence__2__1_9);
property state__pairing__state_to_state_p_sequence__2__1_9;
 state_to_state_p_sequence
|->
 ##1 !RefinementVector[1]
 && RefinementVector[9];
endproperty

state__pairing__state_to_state_p_sequence__3__1_9_a: assert property (disable iff(rst) state__pairing__state_to_state_p_sequence__3__1_9);
property state__pairing__state_to_state_p_sequence__3__1_9;
 state_to_state_p_sequence
|->
 ##1 RefinementVector[1]
 && RefinementVector[9];
endproperty



endmodule
