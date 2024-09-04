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

reset_a_cnt_out_sig_ec: assert property (reset_p_cnt_out_sig_ec);
property reset_p_cnt_out_sig_ec;
  bit unsigned [31:0] cnt_out_sig_store; //Store the value of the output from the generated RTL
  reset_p_sequence
  ##0 (1'b1, cnt_out_sig_store = cntr.cnt_out_sig)
  |->
  ##[0:0] cnt_out_sig_store == cnt;
endproperty

state_to_state_a_cnt_out_sig_ec: assert property (disable iff(rst) state_to_state_p_cnt_out_sig_ec);
property state_to_state_p_cnt_out_sig_ec;
  bit unsigned [31:0] cnt_out_sig_store; //Store the value of the output from the generated RTL
  state_to_state_p_sequence
  ##1 (1'b1, cnt_out_sig_store = cntr.cnt_out_sig)
  |->
  ##[0:7] cnt_out_sig_store == cnt;
endproperty

state_to_state_1_a_cnt_out_sig_ec: assert property (disable iff(rst) state_to_state_1_p_cnt_out_sig_ec);
property state_to_state_1_p_cnt_out_sig_ec;
  bit unsigned [31:0] cnt_out_sig_store; //Store the value of the output from the generated RTL
  state_to_state_1_p_sequence
  ##1 (1'b1, cnt_out_sig_store = cntr.cnt_out_sig)
  |->
  ##[0:7] cnt_out_sig_store == cnt;
endproperty

state_to_state_2_a_cnt_out_sig_ec: assert property (disable iff(rst) state_to_state_2_p_cnt_out_sig_ec);
property state_to_state_2_p_cnt_out_sig_ec;
  bit unsigned [31:0] cnt_out_sig_store; //Store the value of the output from the generated RTL
  state_to_state_2_p_sequence
  ##1 (1'b1, cnt_out_sig_store = cntr.cnt_out_sig)
  |->
  ##[0:7] cnt_out_sig_store == cnt;
endproperty


endmodule
