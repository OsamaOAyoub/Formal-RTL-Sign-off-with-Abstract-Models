`include "processor.sv"
`include "processor_package.sv"
`include "global_package.sv"
`include "proc_states_computational.sv"
`include "proc_states_control.sv"
`include "proc_states_operations.sv"
`include "proc_states_package.sv"
`include "proc_states.sv"

//Wrapper definition
module VerificationWrapper (
  input logic clk,
  input logic reset,
  input TypeInstr instrIn,
  input TypeDataWord dataIn,
  output TypeDataWord dataOut,
  output TypeInstrAddr instrAddr,
  output TypeDataAddr dataAddr,
  output logic writeEnable
);

//DUT instantiation
processor dut_inst (
  .clk(clk),
  .reset(reset),
  .instrIn(instrIn),
  .dataIn(dataIn),
  .dataOut(dataOut),
  .instrAddr(instrAddr),
  .dataAddr(dataAddr),
  .writeEnable(writeEnable)
);


//Generated RTL instantiation
proc_states proc_states (
  .rst(reset),
  .clk(clk),
  .dataaddr_sig(),
  .datain_sig(dataIn),
  .dataout_sig(),
  .instrIn_sig(instrIn),
  .instraddr_sig(),
  .wen_sig()
);

default clocking default_clk @(posedge clk); endclocking

sequence reset_sequence;
  reset ##1 !reset;
endsequence

sequence reset_p_sequence;
  reset_sequence;
endsequence

sequence Decode_to_Fetch_p_sequence;
  (proc_states.proc_states_control_inst.current_state==1) &&
  ((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd7) &&
  (((proc_states.proc_states_computational_inst.instr & 16'd3584) == 16'd0) || ((((proc_states.proc_states_computational_inst.instr & 16'd3584) == 16'd0) ? proc_states.proc_states_computational_inst.reg_file [0] : proc_states.proc_states_computational_inst.reg_file [7]) == 8'd0));
endsequence

sequence Decode_to_Fetch_1_p_sequence;
  (proc_states.proc_states_control_inst.current_state==1) &&
  ((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd7) &&
  !(((proc_states.proc_states_computational_inst.instr & 16'd3584) == 16'd0) || (proc_states.proc_states_computational_inst.reg_file [7] == 8'd0));
endsequence

sequence Decode_to_Fetch_2_p_sequence;
  (proc_states.proc_states_control_inst.current_state==1) &&
  ((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd6);
endsequence

sequence Decode_to_execute_p_sequence;
  (proc_states.proc_states_control_inst.current_state==1) &&
  ((proc_states.proc_states_computational_inst.instr >> 16'd12) != 16'd7) &&
  ((proc_states.proc_states_computational_inst.instr >> 16'd12) != 16'd6);
endsequence

sequence Fetch_to_Decode_p_sequence;
  (proc_states.proc_states_control_inst.current_state==0);
endsequence

sequence execute_to_memory_p_sequence;
  (proc_states.proc_states_control_inst.current_state==2) &&
  ((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd5) &&
  !((((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd1) && ((proc_states.proc_states_computational_inst.instr & 16'd7) == 16'd1)) || ((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd2)) &&
  !((((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd1) && ((proc_states.proc_states_computational_inst.instr & 16'd7) == 16'd2)) || ((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd3)) &&
  (((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd4) || ((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd5));
endsequence

sequence execute_to_memory_1_p_sequence;
  (proc_states.proc_states_control_inst.current_state==2) &&
  ((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd1) &&
  ((((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd1) && ((proc_states.proc_states_computational_inst.instr & 16'd7) == 16'd1)) || ((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd2)) &&
  !((((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd1) && ((proc_states.proc_states_computational_inst.instr & 16'd7) == 16'd2)) || ((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd3)) &&
  !(((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd4) || ((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd5));
endsequence

sequence execute_to_memory_2_p_sequence;
  (proc_states.proc_states_control_inst.current_state==2) &&
  ((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd1) &&
  !((((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd1) && ((proc_states.proc_states_computational_inst.instr & 16'd7) == 16'd1)) || ((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd2)) &&
  ((((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd1) && ((proc_states.proc_states_computational_inst.instr & 16'd7) == 16'd2)) || ((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd3)) &&
  !(((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd4) || ((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd5));
endsequence

sequence execute_to_memory_3_p_sequence;
  (proc_states.proc_states_control_inst.current_state==2) &&
  ((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd1) &&
  !((((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd1) && ((proc_states.proc_states_computational_inst.instr & 16'd7) == 16'd1)) || ((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd2)) &&
  !((((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd1) && ((proc_states.proc_states_computational_inst.instr & 16'd7) == 16'd2)) || ((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd3)) &&
  !(((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd4) || ((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd5));
endsequence

sequence execute_to_memory_4_p_sequence;
  (proc_states.proc_states_control_inst.current_state==2) &&
  ((proc_states.proc_states_computational_inst.instr >> 16'd12) != 16'd5) &&
  ((proc_states.proc_states_computational_inst.instr >> 16'd12) != 16'd1) &&
  (((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd2) || ((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd3)) &&
  ((((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd1) && ((proc_states.proc_states_computational_inst.instr & 16'd7) == 16'd1)) || ((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd2)) &&
  !((((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd1) && ((proc_states.proc_states_computational_inst.instr & 16'd7) == 16'd2)) || ((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd3)) &&
  !(((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd4) || ((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd5));
endsequence

sequence execute_to_memory_5_p_sequence;
  (proc_states.proc_states_control_inst.current_state==2) &&
  ((proc_states.proc_states_computational_inst.instr >> 16'd12) != 16'd5) &&
  ((proc_states.proc_states_computational_inst.instr >> 16'd12) != 16'd1) &&
  (((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd2) || ((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd3)) &&
  !((((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd1) && ((proc_states.proc_states_computational_inst.instr & 16'd7) == 16'd1)) || ((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd2)) &&
  ((((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd1) && ((proc_states.proc_states_computational_inst.instr & 16'd7) == 16'd2)) || ((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd3)) &&
  !(((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd4) || ((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd5));
endsequence

sequence execute_to_memory_6_p_sequence;
  (proc_states.proc_states_control_inst.current_state==2) &&
  ((proc_states.proc_states_computational_inst.instr >> 16'd12) != 16'd5) &&
  ((proc_states.proc_states_computational_inst.instr >> 16'd12) != 16'd1) &&
  !(((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd2) || ((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd3)) &&
  !((((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd1) && ((proc_states.proc_states_computational_inst.instr & 16'd7) == 16'd1)) || ((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd2)) &&
  !((((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd1) && ((proc_states.proc_states_computational_inst.instr & 16'd7) == 16'd2)) || ((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd3)) &&
  (((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd4) || ((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd5));
endsequence

sequence execute_to_memory_7_p_sequence;
  (proc_states.proc_states_control_inst.current_state==2) &&
  ((proc_states.proc_states_computational_inst.instr >> 16'd12) != 16'd5) &&
  ((proc_states.proc_states_computational_inst.instr >> 16'd12) != 16'd1) &&
  !(((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd2) || ((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd3)) &&
  !((((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd1) && ((proc_states.proc_states_computational_inst.instr & 16'd7) == 16'd1)) || ((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd2)) &&
  !((((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd1) && ((proc_states.proc_states_computational_inst.instr & 16'd7) == 16'd2)) || ((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd3)) &&
  !(((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd4) || ((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd5));
endsequence

sequence memory_to_writeback_p_sequence;
  (proc_states.proc_states_control_inst.current_state==3) &&
  ((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd4);
endsequence

sequence memory_to_writeback_1_p_sequence;
  (proc_states.proc_states_control_inst.current_state==3) &&
  ((proc_states.proc_states_computational_inst.instr >> 16'd12) != 16'd4);
endsequence

sequence writeback_to_Fetch_p_sequence;
  (proc_states.proc_states_control_inst.current_state==4) &&
  (((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd4) && ((proc_states.proc_states_computational_inst.instr & 16'd448) != 16'd0)) &&
  !(((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd1) && (((proc_states.proc_states_computational_inst.instr >> 16'd3) & 16'd7) != 16'd0)) &&
  !((((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd2) || ((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd3)) && ((proc_states.proc_states_computational_inst.instr & 16'd448) != 16'd0));
endsequence

sequence writeback_to_Fetch_1_p_sequence;
  (proc_states.proc_states_control_inst.current_state==4) &&
  !(((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd4) && ((proc_states.proc_states_computational_inst.instr & 16'd448) != 16'd0)) &&
  (((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd1) && (((proc_states.proc_states_computational_inst.instr >> 16'd3) & 16'd7) != 16'd0));
endsequence

sequence writeback_to_Fetch_2_p_sequence;
  (proc_states.proc_states_control_inst.current_state==4) &&
  !(((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd4) && ((proc_states.proc_states_computational_inst.instr & 16'd448) != 16'd0)) &&
  !(((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd1) && (((proc_states.proc_states_computational_inst.instr >> 16'd3) & 16'd7) != 16'd0)) &&
  ((((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd2) || ((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd3)) && ((proc_states.proc_states_computational_inst.instr & 16'd448) != 16'd0));
endsequence

sequence writeback_to_Fetch_3_p_sequence;
  (proc_states.proc_states_control_inst.current_state==4) &&
  !(((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd4) && ((proc_states.proc_states_computational_inst.instr & 16'd448) != 16'd0)) &&
  !(((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd1) && (((proc_states.proc_states_computational_inst.instr >> 16'd3) & 16'd7) != 16'd0)) &&
  !((((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd2) || ((proc_states.proc_states_computational_inst.instr >> 16'd12) == 16'd3)) && ((proc_states.proc_states_computational_inst.instr & 16'd448) != 16'd0));
endsequence

reset_a_dataaddr_sig_ec: assert property (reset_p_dataaddr_sig_ec);
property reset_p_dataaddr_sig_ec;
  bit unsigned [7:0] dataaddr_sig_store; //Store the value of the output from the generated RTL
  reset_p_sequence
  ##0 (1'b1, dataaddr_sig_store = proc_states.dataaddr_sig)
  |->
  ##[0:1] (dataaddr_sig_store == dataAddr);
endproperty

reset_a_dataout_sig_ec: assert property (reset_p_dataout_sig_ec);
property reset_p_dataout_sig_ec;
  bit unsigned [7:0] dataout_sig_store; //Store the value of the output from the generated RTL
  reset_p_sequence
  ##0 (1'b1, dataout_sig_store = proc_states.dataout_sig)
  |->
  ##[0:1] dataout_sig_store == dataOut;
endproperty

reset_a_instraddr_sig_ec: assert property (reset_p_instraddr_sig_ec);
property reset_p_instraddr_sig_ec;
  bit unsigned [15:0] instraddr_sig_store; //Store the value of the output from the generated RTL
  reset_p_sequence
  ##0 (1'b1, instraddr_sig_store = proc_states.instraddr_sig)
  |->
  ##[0:1] (instraddr_sig_store == instrAddr);
endproperty

reset_a_wen_sig_ec: assert property (reset_p_wen_sig_ec);
property reset_p_wen_sig_ec;
  bit wen_sig_store; //Store the value of the output from the generated RTL
  reset_p_sequence
  ##0 (1'b1, wen_sig_store = proc_states.wen_sig)
  |->
  ##[0:1] (wen_sig_store == writeEnable);
endproperty

Decode_to_Fetch_a_dataaddr_sig_ec: assert property (disable iff(reset) Decode_to_Fetch_p_dataaddr_sig_ec);
property Decode_to_Fetch_p_dataaddr_sig_ec;
  bit unsigned [7:0] dataaddr_sig_store; //Store the value of the output from the generated RTL
  Decode_to_Fetch_p_sequence
  ##1 (1'b1, dataaddr_sig_store = proc_states.dataaddr_sig)
  |->
  ##[0:1] (dataaddr_sig_store == dataAddr);
endproperty

Decode_to_Fetch_a_dataout_sig_ec: assert property (disable iff(reset) Decode_to_Fetch_p_dataout_sig_ec);
property Decode_to_Fetch_p_dataout_sig_ec;
  bit unsigned [7:0] dataout_sig_store; //Store the value of the output from the generated RTL
  Decode_to_Fetch_p_sequence
  ##1 (1'b1, dataout_sig_store = proc_states.dataout_sig)
  |->
  ##[0:1] (dataout_sig_store == dataOut);
endproperty

Decode_to_Fetch_a_instraddr_sig_ec: assert property (disable iff(reset) Decode_to_Fetch_p_instraddr_sig_ec);
property Decode_to_Fetch_p_instraddr_sig_ec;
  bit unsigned [15:0] instraddr_sig_store; //Store the value of the output from the generated RTL
  Decode_to_Fetch_p_sequence
  ##1 (1'b1, instraddr_sig_store = proc_states.instraddr_sig)
  |->
  ##[0:1] (instraddr_sig_store == instrAddr);
endproperty

Decode_to_Fetch_a_wen_sig_ec: assert property (disable iff(reset) Decode_to_Fetch_p_wen_sig_ec);
property Decode_to_Fetch_p_wen_sig_ec;
  bit wen_sig_store; //Store the value of the output from the generated RTL
  Decode_to_Fetch_p_sequence
  ##1 (1'b1, wen_sig_store = proc_states.wen_sig)
  |->
  ##[0:1] (wen_sig_store == writeEnable);
endproperty

Decode_to_Fetch_1_a_dataaddr_sig_ec: assert property (disable iff(reset) Decode_to_Fetch_1_p_dataaddr_sig_ec);
property Decode_to_Fetch_1_p_dataaddr_sig_ec;
  bit unsigned [7:0] dataaddr_sig_store; //Store the value of the output from the generated RTL
  Decode_to_Fetch_1_p_sequence
  ##1 (1'b1, dataaddr_sig_store = proc_states.dataaddr_sig)
  |->
  ##[0:1] (dataaddr_sig_store == dataAddr);
endproperty

Decode_to_Fetch_1_a_dataout_sig_ec: assert property (disable iff(reset) Decode_to_Fetch_1_p_dataout_sig_ec);
property Decode_to_Fetch_1_p_dataout_sig_ec;
  bit unsigned [7:0] dataout_sig_store; //Store the value of the output from the generated RTL
  Decode_to_Fetch_1_p_sequence
  ##1 (1'b1, dataout_sig_store = proc_states.dataout_sig)
  |->
  ##[0:1] (dataout_sig_store == dataOut);
endproperty

Decode_to_Fetch_1_a_instraddr_sig_ec: assert property (disable iff(reset) Decode_to_Fetch_1_p_instraddr_sig_ec);
property Decode_to_Fetch_1_p_instraddr_sig_ec;
  bit unsigned [15:0] instraddr_sig_store; //Store the value of the output from the generated RTL
  Decode_to_Fetch_1_p_sequence
  ##1 (1'b1, instraddr_sig_store = proc_states.instraddr_sig)
  |->
  ##[0:1] (instraddr_sig_store == instrAddr);
endproperty

Decode_to_Fetch_1_a_wen_sig_ec: assert property (disable iff(reset) Decode_to_Fetch_1_p_wen_sig_ec);
property Decode_to_Fetch_1_p_wen_sig_ec;
  bit wen_sig_store; //Store the value of the output from the generated RTL
  Decode_to_Fetch_1_p_sequence
  ##1 (1'b1, wen_sig_store = proc_states.wen_sig)
  |->
  ##[0:1] (wen_sig_store == writeEnable);
endproperty

Decode_to_Fetch_2_a_dataaddr_sig_ec: assert property (disable iff(reset) Decode_to_Fetch_2_p_dataaddr_sig_ec);
property Decode_to_Fetch_2_p_dataaddr_sig_ec;
  bit unsigned [7:0] dataaddr_sig_store; //Store the value of the output from the generated RTL
  Decode_to_Fetch_2_p_sequence
  ##1 (1'b1, dataaddr_sig_store = proc_states.dataaddr_sig)
  |->
  ##[0:1] (dataaddr_sig_store == dataAddr);
endproperty

Decode_to_Fetch_2_a_dataout_sig_ec: assert property (disable iff(reset) Decode_to_Fetch_2_p_dataout_sig_ec);
property Decode_to_Fetch_2_p_dataout_sig_ec;
  bit unsigned [7:0] dataout_sig_store; //Store the value of the output from the generated RTL
  Decode_to_Fetch_2_p_sequence
  ##1 (1'b1, dataout_sig_store = proc_states.dataout_sig)
  |->
  ##[0:1] (dataout_sig_store == dataOut);
endproperty

Decode_to_Fetch_2_a_instraddr_sig_ec: assert property (disable iff(reset) Decode_to_Fetch_2_p_instraddr_sig_ec);
property Decode_to_Fetch_2_p_instraddr_sig_ec;
  bit unsigned [15:0] instraddr_sig_store; //Store the value of the output from the generated RTL
  Decode_to_Fetch_2_p_sequence
  ##1 (1'b1, instraddr_sig_store = proc_states.instraddr_sig)
  |->
  ##[0:1] (instraddr_sig_store == instrAddr);
endproperty

Decode_to_Fetch_2_a_wen_sig_ec: assert property (disable iff(reset) Decode_to_Fetch_2_p_wen_sig_ec);
property Decode_to_Fetch_2_p_wen_sig_ec;
  bit wen_sig_store; //Store the value of the output from the generated RTL
  Decode_to_Fetch_2_p_sequence
  ##1 (1'b1, wen_sig_store = proc_states.wen_sig)
  |->
  ##[0:1] (wen_sig_store == writeEnable);
endproperty

Decode_to_execute_a_dataaddr_sig_ec: assert property (disable iff(reset) Decode_to_execute_p_dataaddr_sig_ec);
property Decode_to_execute_p_dataaddr_sig_ec;
  bit unsigned [7:0] dataaddr_sig_store; //Store the value of the output from the generated RTL
  Decode_to_execute_p_sequence
  ##1 (1'b1, dataaddr_sig_store = proc_states.dataaddr_sig)
  |->
  ##[0:1] (dataaddr_sig_store == dataAddr);
endproperty

Decode_to_execute_a_dataout_sig_ec: assert property (disable iff(reset) Decode_to_execute_p_dataout_sig_ec);
property Decode_to_execute_p_dataout_sig_ec;
  bit unsigned [7:0] dataout_sig_store; //Store the value of the output from the generated RTL
  Decode_to_execute_p_sequence
  ##1 (1'b1, dataout_sig_store = proc_states.dataout_sig)
  |->
  ##[0:1] (dataout_sig_store == dataOut);
endproperty

Decode_to_execute_a_instraddr_sig_ec: assert property (disable iff(reset) Decode_to_execute_p_instraddr_sig_ec);
property Decode_to_execute_p_instraddr_sig_ec;
  bit unsigned [15:0] instraddr_sig_store; //Store the value of the output from the generated RTL
  Decode_to_execute_p_sequence
  ##1 (1'b1, instraddr_sig_store = proc_states.instraddr_sig)
  |->
  ##[0:1] (instraddr_sig_store == instrAddr);
endproperty

Decode_to_execute_a_wen_sig_ec: assert property (disable iff(reset) Decode_to_execute_p_wen_sig_ec);
property Decode_to_execute_p_wen_sig_ec;
  bit wen_sig_store; //Store the value of the output from the generated RTL
  Decode_to_execute_p_sequence
  ##1 (1'b1, wen_sig_store = proc_states.wen_sig)
  |->
  ##[0:1] (wen_sig_store == writeEnable);
endproperty

Fetch_to_Decode_a_dataaddr_sig_ec: assert property (disable iff(reset) Fetch_to_Decode_p_dataaddr_sig_ec);
property Fetch_to_Decode_p_dataaddr_sig_ec;
  bit unsigned [7:0] dataaddr_sig_store; //Store the value of the output from the generated RTL
  Fetch_to_Decode_p_sequence
  ##1 (1'b1, dataaddr_sig_store = proc_states.dataaddr_sig)
  |->
  ##[0:1] (dataaddr_sig_store == dataAddr);
endproperty

Fetch_to_Decode_a_dataout_sig_ec: assert property (disable iff(reset) Fetch_to_Decode_p_dataout_sig_ec);
property Fetch_to_Decode_p_dataout_sig_ec;
  bit unsigned [7:0] dataout_sig_store; //Store the value of the output from the generated RTL
  Fetch_to_Decode_p_sequence
  ##1 (1'b1, dataout_sig_store = proc_states.dataout_sig)
  |->
  ##[0:1] (dataout_sig_store == dataOut);
endproperty

Fetch_to_Decode_a_instraddr_sig_ec: assert property (disable iff(reset) Fetch_to_Decode_p_instraddr_sig_ec);
property Fetch_to_Decode_p_instraddr_sig_ec;
  bit unsigned [15:0] instraddr_sig_store; //Store the value of the output from the generated RTL
  Fetch_to_Decode_p_sequence
  ##1 (1'b1, instraddr_sig_store = proc_states.instraddr_sig)
  |->
  ##[0:1] (instraddr_sig_store == instrAddr);
endproperty

Fetch_to_Decode_a_wen_sig_ec: assert property (disable iff(reset) Fetch_to_Decode_p_wen_sig_ec);
property Fetch_to_Decode_p_wen_sig_ec;
  bit wen_sig_store; //Store the value of the output from the generated RTL
  Fetch_to_Decode_p_sequence
  ##1 (1'b1, wen_sig_store = proc_states.wen_sig)
  |->
  ##[0:1] (wen_sig_store == writeEnable);
endproperty

execute_to_memory_a_dataaddr_sig_ec: assert property (disable iff(reset) execute_to_memory_p_dataaddr_sig_ec);
property execute_to_memory_p_dataaddr_sig_ec;
  bit unsigned [7:0] dataaddr_sig_store; //Store the value of the output from the generated RTL
  execute_to_memory_p_sequence
  ##1 (1'b1, dataaddr_sig_store = proc_states.dataaddr_sig)
  |->
  ##[0:1] (dataaddr_sig_store == dataAddr);
endproperty

execute_to_memory_a_dataout_sig_ec: assert property (disable iff(reset) execute_to_memory_p_dataout_sig_ec);
property execute_to_memory_p_dataout_sig_ec;
  bit unsigned [7:0] dataout_sig_store; //Store the value of the output from the generated RTL
  execute_to_memory_p_sequence
  ##1 (1'b1, dataout_sig_store = proc_states.dataout_sig)
  |->
  ##[0:1] (dataout_sig_store == dataOut);
endproperty

execute_to_memory_a_instraddr_sig_ec: assert property (disable iff(reset) execute_to_memory_p_instraddr_sig_ec);
property execute_to_memory_p_instraddr_sig_ec;
  bit unsigned [15:0] instraddr_sig_store; //Store the value of the output from the generated RTL
  execute_to_memory_p_sequence
  ##1 (1'b1, instraddr_sig_store = proc_states.instraddr_sig)
  |->
  ##[0:1] (instraddr_sig_store == instrAddr);
endproperty

execute_to_memory_a_wen_sig_ec: assert property (disable iff(reset) execute_to_memory_p_wen_sig_ec);
property execute_to_memory_p_wen_sig_ec;
  bit wen_sig_store; //Store the value of the output from the generated RTL
  execute_to_memory_p_sequence
  ##1 (1'b1, wen_sig_store = proc_states.wen_sig)
  |->
  ##[0:1] (wen_sig_store == writeEnable);
endproperty

execute_to_memory_1_a_dataaddr_sig_ec: assert property (disable iff(reset) execute_to_memory_1_p_dataaddr_sig_ec);
property execute_to_memory_1_p_dataaddr_sig_ec;
  bit unsigned [7:0] dataaddr_sig_store; //Store the value of the output from the generated RTL
  execute_to_memory_1_p_sequence
  ##1 (1'b1, dataaddr_sig_store = proc_states.dataaddr_sig)
  |->
  ##[0:1] (dataaddr_sig_store == dataAddr);
endproperty

execute_to_memory_1_a_dataout_sig_ec: assert property (disable iff(reset) execute_to_memory_1_p_dataout_sig_ec);
property execute_to_memory_1_p_dataout_sig_ec;
  bit unsigned [7:0] dataout_sig_store; //Store the value of the output from the generated RTL
  execute_to_memory_1_p_sequence
  ##1 (1'b1, dataout_sig_store = proc_states.dataout_sig)
  |->
  ##[0:1] (dataout_sig_store == dataOut);
endproperty

execute_to_memory_1_a_instraddr_sig_ec: assert property (disable iff(reset) execute_to_memory_1_p_instraddr_sig_ec);
property execute_to_memory_1_p_instraddr_sig_ec;
  bit unsigned [15:0] instraddr_sig_store; //Store the value of the output from the generated RTL
  execute_to_memory_1_p_sequence
  ##1 (1'b1, instraddr_sig_store = proc_states.instraddr_sig)
  |->
  ##[0:1] (instraddr_sig_store == instrAddr);
endproperty

execute_to_memory_1_a_wen_sig_ec: assert property (disable iff(reset) execute_to_memory_1_p_wen_sig_ec);
property execute_to_memory_1_p_wen_sig_ec;
  bit wen_sig_store; //Store the value of the output from the generated RTL
  execute_to_memory_1_p_sequence
  ##1 (1'b1, wen_sig_store = proc_states.wen_sig)
  |->
  ##[0:1] (wen_sig_store == writeEnable);
endproperty

execute_to_memory_2_a_dataaddr_sig_ec: assert property (disable iff(reset) execute_to_memory_2_p_dataaddr_sig_ec);
property execute_to_memory_2_p_dataaddr_sig_ec;
  bit unsigned [7:0] dataaddr_sig_store; //Store the value of the output from the generated RTL
  execute_to_memory_2_p_sequence
  ##1 (1'b1, dataaddr_sig_store = proc_states.dataaddr_sig)
  |->
  ##[0:1] (dataaddr_sig_store == dataAddr);
endproperty

execute_to_memory_2_a_dataout_sig_ec: assert property (disable iff(reset) execute_to_memory_2_p_dataout_sig_ec);
property execute_to_memory_2_p_dataout_sig_ec;
  bit unsigned [7:0] dataout_sig_store; //Store the value of the output from the generated RTL
  execute_to_memory_2_p_sequence
  ##1 (1'b1, dataout_sig_store = proc_states.dataout_sig)
  |->
  ##[0:1] (dataout_sig_store == dataOut);
endproperty

execute_to_memory_2_a_instraddr_sig_ec: assert property (disable iff(reset) execute_to_memory_2_p_instraddr_sig_ec);
property execute_to_memory_2_p_instraddr_sig_ec;
  bit unsigned [15:0] instraddr_sig_store; //Store the value of the output from the generated RTL
  execute_to_memory_2_p_sequence
  ##1 (1'b1, instraddr_sig_store = proc_states.instraddr_sig)
  |->
  ##[0:1] (instraddr_sig_store == instrAddr);
endproperty

execute_to_memory_2_a_wen_sig_ec: assert property (disable iff(reset) execute_to_memory_2_p_wen_sig_ec);
property execute_to_memory_2_p_wen_sig_ec;
  bit wen_sig_store; //Store the value of the output from the generated RTL
  execute_to_memory_2_p_sequence
  ##1 (1'b1, wen_sig_store = proc_states.wen_sig)
  |->
  ##[0:1] (wen_sig_store == writeEnable);
endproperty

execute_to_memory_3_a_dataaddr_sig_ec: assert property (disable iff(reset) execute_to_memory_3_p_dataaddr_sig_ec);
property execute_to_memory_3_p_dataaddr_sig_ec;
  bit unsigned [7:0] dataaddr_sig_store; //Store the value of the output from the generated RTL
  execute_to_memory_3_p_sequence
  ##1 (1'b1, dataaddr_sig_store = proc_states.dataaddr_sig)
  |->
  ##[0:1] (dataaddr_sig_store == dataAddr);
endproperty

execute_to_memory_3_a_dataout_sig_ec: assert property (disable iff(reset) execute_to_memory_3_p_dataout_sig_ec);
property execute_to_memory_3_p_dataout_sig_ec;
  bit unsigned [7:0] dataout_sig_store; //Store the value of the output from the generated RTL
  execute_to_memory_3_p_sequence
  ##1 (1'b1, dataout_sig_store = proc_states.dataout_sig)
  |->
  ##[0:1] (dataout_sig_store == dataOut);
endproperty

execute_to_memory_3_a_instraddr_sig_ec: assert property (disable iff(reset) execute_to_memory_3_p_instraddr_sig_ec);
property execute_to_memory_3_p_instraddr_sig_ec;
  bit unsigned [15:0] instraddr_sig_store; //Store the value of the output from the generated RTL
  execute_to_memory_3_p_sequence
  ##1 (1'b1, instraddr_sig_store = proc_states.instraddr_sig)
  |->
  ##[0:1] (instraddr_sig_store == instrAddr);
endproperty

execute_to_memory_3_a_wen_sig_ec: assert property (disable iff(reset) execute_to_memory_3_p_wen_sig_ec);
property execute_to_memory_3_p_wen_sig_ec;
  bit wen_sig_store; //Store the value of the output from the generated RTL
  execute_to_memory_3_p_sequence
  ##1 (1'b1, wen_sig_store = proc_states.wen_sig)
  |->
  ##[0:1] (wen_sig_store == writeEnable);
endproperty

execute_to_memory_4_a_dataaddr_sig_ec: assert property (disable iff(reset) execute_to_memory_4_p_dataaddr_sig_ec);
property execute_to_memory_4_p_dataaddr_sig_ec;
  bit unsigned [7:0] dataaddr_sig_store; //Store the value of the output from the generated RTL
  execute_to_memory_4_p_sequence
  ##1 (1'b1, dataaddr_sig_store = proc_states.dataaddr_sig)
  |->
  ##[0:1] (dataaddr_sig_store == dataAddr);
endproperty

execute_to_memory_4_a_dataout_sig_ec: assert property (disable iff(reset) execute_to_memory_4_p_dataout_sig_ec);
property execute_to_memory_4_p_dataout_sig_ec;
  bit unsigned [7:0] dataout_sig_store; //Store the value of the output from the generated RTL
  execute_to_memory_4_p_sequence
  ##1 (1'b1, dataout_sig_store = proc_states.dataout_sig)
  |->
  ##[0:1] (dataout_sig_store == dataOut);
endproperty

execute_to_memory_4_a_instraddr_sig_ec: assert property (disable iff(reset) execute_to_memory_4_p_instraddr_sig_ec);
property execute_to_memory_4_p_instraddr_sig_ec;
  bit unsigned [15:0] instraddr_sig_store; //Store the value of the output from the generated RTL
  execute_to_memory_4_p_sequence
  ##1 (1'b1, instraddr_sig_store = proc_states.instraddr_sig)
  |->
  ##[0:1] (instraddr_sig_store == instrAddr);
endproperty

execute_to_memory_4_a_wen_sig_ec: assert property (disable iff(reset) execute_to_memory_4_p_wen_sig_ec);
property execute_to_memory_4_p_wen_sig_ec;
  bit wen_sig_store; //Store the value of the output from the generated RTL
  execute_to_memory_4_p_sequence
  ##1 (1'b1, wen_sig_store = proc_states.wen_sig)
  |->
  ##[0:1] (wen_sig_store == writeEnable);
endproperty

execute_to_memory_5_a_dataaddr_sig_ec: assert property (disable iff(reset) execute_to_memory_5_p_dataaddr_sig_ec);
property execute_to_memory_5_p_dataaddr_sig_ec;
  bit unsigned [7:0] dataaddr_sig_store; //Store the value of the output from the generated RTL
  execute_to_memory_5_p_sequence
  ##1 (1'b1, dataaddr_sig_store = proc_states.dataaddr_sig)
  |->
  ##[0:1] (dataaddr_sig_store == dataAddr);
endproperty

execute_to_memory_5_a_dataout_sig_ec: assert property (disable iff(reset) execute_to_memory_5_p_dataout_sig_ec);
property execute_to_memory_5_p_dataout_sig_ec;
  bit unsigned [7:0] dataout_sig_store; //Store the value of the output from the generated RTL
  execute_to_memory_5_p_sequence
  ##1 (1'b1, dataout_sig_store = proc_states.dataout_sig)
  |->
  ##[0:1] (dataout_sig_store == dataOut);
endproperty

execute_to_memory_5_a_instraddr_sig_ec: assert property (disable iff(reset) execute_to_memory_5_p_instraddr_sig_ec);
property execute_to_memory_5_p_instraddr_sig_ec;
  bit unsigned [15:0] instraddr_sig_store; //Store the value of the output from the generated RTL
  execute_to_memory_5_p_sequence
  ##1 (1'b1, instraddr_sig_store = proc_states.instraddr_sig)
  |->
  ##[0:1] (instraddr_sig_store == instrAddr);
endproperty

execute_to_memory_5_a_wen_sig_ec: assert property (disable iff(reset) execute_to_memory_5_p_wen_sig_ec);
property execute_to_memory_5_p_wen_sig_ec;
  bit wen_sig_store; //Store the value of the output from the generated RTL
  execute_to_memory_5_p_sequence
  ##1 (1'b1, wen_sig_store = proc_states.wen_sig)
  |->
  ##[0:1] (wen_sig_store == writeEnable);
endproperty

execute_to_memory_6_a_dataaddr_sig_ec: assert property (disable iff(reset) execute_to_memory_6_p_dataaddr_sig_ec);
property execute_to_memory_6_p_dataaddr_sig_ec;
  bit unsigned [7:0] dataaddr_sig_store; //Store the value of the output from the generated RTL
  execute_to_memory_6_p_sequence
  ##1 (1'b1, dataaddr_sig_store = proc_states.dataaddr_sig)
  |->
  ##[0:1] (dataaddr_sig_store == dataAddr);
endproperty

execute_to_memory_6_a_dataout_sig_ec: assert property (disable iff(reset) execute_to_memory_6_p_dataout_sig_ec);
property execute_to_memory_6_p_dataout_sig_ec;
  bit unsigned [7:0] dataout_sig_store; //Store the value of the output from the generated RTL
  execute_to_memory_6_p_sequence
  ##1 (1'b1, dataout_sig_store = proc_states.dataout_sig)
  |->
  ##[0:1] (dataout_sig_store == dataOut);
endproperty

execute_to_memory_6_a_instraddr_sig_ec: assert property (disable iff(reset) execute_to_memory_6_p_instraddr_sig_ec);
property execute_to_memory_6_p_instraddr_sig_ec;
  bit unsigned [15:0] instraddr_sig_store; //Store the value of the output from the generated RTL
  execute_to_memory_6_p_sequence
  ##1 (1'b1, instraddr_sig_store = proc_states.instraddr_sig)
  |->
  ##[0:1] (instraddr_sig_store == instrAddr);
endproperty

execute_to_memory_6_a_wen_sig_ec: assert property (disable iff(reset) execute_to_memory_6_p_wen_sig_ec);
property execute_to_memory_6_p_wen_sig_ec;
  bit wen_sig_store; //Store the value of the output from the generated RTL
  execute_to_memory_6_p_sequence
  ##1 (1'b1, wen_sig_store = proc_states.wen_sig)
  |->
  ##[0:1] (wen_sig_store == writeEnable);
endproperty

execute_to_memory_7_a_dataaddr_sig_ec: assert property (disable iff(reset) execute_to_memory_7_p_dataaddr_sig_ec);
property execute_to_memory_7_p_dataaddr_sig_ec;
  bit unsigned [7:0] dataaddr_sig_store; //Store the value of the output from the generated RTL
  execute_to_memory_7_p_sequence
  ##1 (1'b1, dataaddr_sig_store = proc_states.dataaddr_sig)
  |->
  ##[0:1] (dataaddr_sig_store == dataAddr);
endproperty

execute_to_memory_7_a_dataout_sig_ec: assert property (disable iff(reset) execute_to_memory_7_p_dataout_sig_ec);
property execute_to_memory_7_p_dataout_sig_ec;
  bit unsigned [7:0] dataout_sig_store; //Store the value of the output from the generated RTL
  execute_to_memory_7_p_sequence
  ##1 (1'b1, dataout_sig_store = proc_states.dataout_sig)
  |->
  ##[0:1] (dataout_sig_store == dataOut);
endproperty

execute_to_memory_7_a_instraddr_sig_ec: assert property (disable iff(reset) execute_to_memory_7_p_instraddr_sig_ec);
property execute_to_memory_7_p_instraddr_sig_ec;
  bit unsigned [15:0] instraddr_sig_store; //Store the value of the output from the generated RTL
  execute_to_memory_7_p_sequence
  ##1 (1'b1, instraddr_sig_store = proc_states.instraddr_sig)
  |->
  ##[0:1] (instraddr_sig_store == instrAddr);
endproperty

execute_to_memory_7_a_wen_sig_ec: assert property (disable iff(reset) execute_to_memory_7_p_wen_sig_ec);
property execute_to_memory_7_p_wen_sig_ec;
  bit wen_sig_store; //Store the value of the output from the generated RTL
  execute_to_memory_7_p_sequence
  ##1 (1'b1, wen_sig_store = proc_states.wen_sig)
  |->
  ##[0:1] (wen_sig_store == writeEnable);
endproperty

memory_to_writeback_a_dataaddr_sig_ec: assert property (disable iff(reset) memory_to_writeback_p_dataaddr_sig_ec);
property memory_to_writeback_p_dataaddr_sig_ec;
  bit unsigned [7:0] dataaddr_sig_store; //Store the value of the output from the generated RTL
  memory_to_writeback_p_sequence
  ##1 (1'b1, dataaddr_sig_store = proc_states.dataaddr_sig)
  |->
  ##[0:1] (dataaddr_sig_store == dataAddr);
endproperty

memory_to_writeback_a_dataout_sig_ec: assert property (disable iff(reset) memory_to_writeback_p_dataout_sig_ec);
property memory_to_writeback_p_dataout_sig_ec;
  bit unsigned [7:0] dataout_sig_store; //Store the value of the output from the generated RTL
  memory_to_writeback_p_sequence
  ##1 (1'b1, dataout_sig_store = proc_states.dataout_sig)
  |->
  ##[0:1] (dataout_sig_store == dataOut);
endproperty

memory_to_writeback_a_instraddr_sig_ec: assert property (disable iff(reset) memory_to_writeback_p_instraddr_sig_ec);
property memory_to_writeback_p_instraddr_sig_ec;
  bit unsigned [15:0] instraddr_sig_store; //Store the value of the output from the generated RTL
  memory_to_writeback_p_sequence
  ##1 (1'b1, instraddr_sig_store = proc_states.instraddr_sig)
  |->
  ##[0:1] (instraddr_sig_store == instrAddr);
endproperty

memory_to_writeback_a_wen_sig_ec: assert property (disable iff(reset) memory_to_writeback_p_wen_sig_ec);
property memory_to_writeback_p_wen_sig_ec;
  bit wen_sig_store; //Store the value of the output from the generated RTL
  memory_to_writeback_p_sequence
  ##1 (1'b1, wen_sig_store = proc_states.wen_sig)
  |->
  ##[0:1] (wen_sig_store == writeEnable);
endproperty

memory_to_writeback_1_a_dataaddr_sig_ec: assert property (disable iff(reset) memory_to_writeback_1_p_dataaddr_sig_ec);
property memory_to_writeback_1_p_dataaddr_sig_ec;
  bit unsigned [7:0] dataaddr_sig_store; //Store the value of the output from the generated RTL
  memory_to_writeback_1_p_sequence
  ##1 (1'b1, dataaddr_sig_store = proc_states.dataaddr_sig)
  |->
  ##[0:1] (dataaddr_sig_store == dataAddr);
endproperty

memory_to_writeback_1_a_dataout_sig_ec: assert property (disable iff(reset) memory_to_writeback_1_p_dataout_sig_ec);
property memory_to_writeback_1_p_dataout_sig_ec;
  bit unsigned [7:0] dataout_sig_store; //Store the value of the output from the generated RTL
  memory_to_writeback_1_p_sequence
  ##1 (1'b1, dataout_sig_store = proc_states.dataout_sig)
  |->
  ##[0:1] (dataout_sig_store == dataOut);
endproperty

memory_to_writeback_1_a_instraddr_sig_ec: assert property (disable iff(reset) memory_to_writeback_1_p_instraddr_sig_ec);
property memory_to_writeback_1_p_instraddr_sig_ec;
  bit unsigned [15:0] instraddr_sig_store; //Store the value of the output from the generated RTL
  memory_to_writeback_1_p_sequence
  ##1 (1'b1, instraddr_sig_store = proc_states.instraddr_sig)
  |->
  ##[0:1] (instraddr_sig_store == instrAddr);
endproperty

memory_to_writeback_1_a_wen_sig_ec: assert property (disable iff(reset) memory_to_writeback_1_p_wen_sig_ec);
property memory_to_writeback_1_p_wen_sig_ec;
  bit wen_sig_store; //Store the value of the output from the generated RTL
  memory_to_writeback_1_p_sequence
  ##1 (1'b1, wen_sig_store = proc_states.wen_sig)
  |->
  ##[0:1] (wen_sig_store == writeEnable);
endproperty

writeback_to_Fetch_a_dataaddr_sig_ec: assert property (disable iff(reset) writeback_to_Fetch_p_dataaddr_sig_ec);
property writeback_to_Fetch_p_dataaddr_sig_ec;
  bit unsigned [7:0] dataaddr_sig_store; //Store the value of the output from the generated RTL
  writeback_to_Fetch_p_sequence
  ##1 (1'b1, dataaddr_sig_store = proc_states.dataaddr_sig)
  |->
  ##[0:1] (dataaddr_sig_store == dataAddr);
endproperty

writeback_to_Fetch_a_dataout_sig_ec: assert property (disable iff(reset) writeback_to_Fetch_p_dataout_sig_ec);
property writeback_to_Fetch_p_dataout_sig_ec;
  bit unsigned [7:0] dataout_sig_store; //Store the value of the output from the generated RTL
  writeback_to_Fetch_p_sequence
  ##1 (1'b1, dataout_sig_store = proc_states.dataout_sig)
  |->
  ##[0:1] (dataout_sig_store == dataOut);
endproperty

writeback_to_Fetch_a_instraddr_sig_ec: assert property (disable iff(reset) writeback_to_Fetch_p_instraddr_sig_ec);
property writeback_to_Fetch_p_instraddr_sig_ec;
  bit unsigned [15:0] instraddr_sig_store; //Store the value of the output from the generated RTL
  writeback_to_Fetch_p_sequence
  ##1 (1'b1, instraddr_sig_store = proc_states.instraddr_sig)
  |->
  ##[0:1] (instraddr_sig_store == instrAddr);
endproperty

writeback_to_Fetch_a_wen_sig_ec: assert property (disable iff(reset) writeback_to_Fetch_p_wen_sig_ec);
property writeback_to_Fetch_p_wen_sig_ec;
  bit wen_sig_store; //Store the value of the output from the generated RTL
  writeback_to_Fetch_p_sequence
  ##1 (1'b1, wen_sig_store = proc_states.wen_sig)
  |->
  ##[0:1] (wen_sig_store == writeEnable);
endproperty

writeback_to_Fetch_1_a_dataaddr_sig_ec: assert property (disable iff(reset) writeback_to_Fetch_1_p_dataaddr_sig_ec);
property writeback_to_Fetch_1_p_dataaddr_sig_ec;
  bit unsigned [7:0] dataaddr_sig_store; //Store the value of the output from the generated RTL
  writeback_to_Fetch_1_p_sequence
  ##1 (1'b1, dataaddr_sig_store = proc_states.dataaddr_sig)
  |->
  ##[0:1] (dataaddr_sig_store == dataAddr);
endproperty

writeback_to_Fetch_1_a_dataout_sig_ec: assert property (disable iff(reset) writeback_to_Fetch_1_p_dataout_sig_ec);
property writeback_to_Fetch_1_p_dataout_sig_ec;
  bit unsigned [7:0] dataout_sig_store; //Store the value of the output from the generated RTL
  writeback_to_Fetch_1_p_sequence
  ##1 (1'b1, dataout_sig_store = proc_states.dataout_sig)
  |->
  ##[0:1] (dataout_sig_store == dataOut);
endproperty

writeback_to_Fetch_1_a_instraddr_sig_ec: assert property (disable iff(reset) writeback_to_Fetch_1_p_instraddr_sig_ec);
property writeback_to_Fetch_1_p_instraddr_sig_ec;
  bit unsigned [15:0] instraddr_sig_store; //Store the value of the output from the generated RTL
  writeback_to_Fetch_1_p_sequence
  ##1 (1'b1, instraddr_sig_store = proc_states.instraddr_sig)
  |->
  ##[0:1] (instraddr_sig_store == instrAddr);
endproperty

writeback_to_Fetch_1_a_wen_sig_ec: assert property (disable iff(reset) writeback_to_Fetch_1_p_wen_sig_ec);
property writeback_to_Fetch_1_p_wen_sig_ec;
  bit wen_sig_store; //Store the value of the output from the generated RTL
  writeback_to_Fetch_1_p_sequence
  ##1 (1'b1, wen_sig_store = proc_states.wen_sig)
  |->
  ##[0:1] (wen_sig_store == writeEnable);
endproperty

writeback_to_Fetch_2_a_dataaddr_sig_ec: assert property (disable iff(reset) writeback_to_Fetch_2_p_dataaddr_sig_ec);
property writeback_to_Fetch_2_p_dataaddr_sig_ec;
  bit unsigned [7:0] dataaddr_sig_store; //Store the value of the output from the generated RTL
  writeback_to_Fetch_2_p_sequence
  ##1 (1'b1, dataaddr_sig_store = proc_states.dataaddr_sig)
  |->
  ##[0:1] (dataaddr_sig_store == dataAddr);
endproperty

writeback_to_Fetch_2_a_dataout_sig_ec: assert property (disable iff(reset) writeback_to_Fetch_2_p_dataout_sig_ec);
property writeback_to_Fetch_2_p_dataout_sig_ec;
  bit unsigned [7:0] dataout_sig_store; //Store the value of the output from the generated RTL
  writeback_to_Fetch_2_p_sequence
  ##1 (1'b1, dataout_sig_store = proc_states.dataout_sig)
  |->
  ##[0:1] (dataout_sig_store == dataOut);
endproperty

writeback_to_Fetch_2_a_instraddr_sig_ec: assert property (disable iff(reset) writeback_to_Fetch_2_p_instraddr_sig_ec);
property writeback_to_Fetch_2_p_instraddr_sig_ec;
  bit unsigned [15:0] instraddr_sig_store; //Store the value of the output from the generated RTL
  writeback_to_Fetch_2_p_sequence
  ##1 (1'b1, instraddr_sig_store = proc_states.instraddr_sig)
  |->
  ##[0:1] (instraddr_sig_store == instrAddr);
endproperty

writeback_to_Fetch_2_a_wen_sig_ec: assert property (disable iff(reset) writeback_to_Fetch_2_p_wen_sig_ec);
property writeback_to_Fetch_2_p_wen_sig_ec;
  bit wen_sig_store; //Store the value of the output from the generated RTL
  writeback_to_Fetch_2_p_sequence
  ##1 (1'b1, wen_sig_store = proc_states.wen_sig)
  |->
  ##[0:1] (wen_sig_store == writeEnable);
endproperty

writeback_to_Fetch_3_a_dataaddr_sig_ec: assert property (disable iff(reset) writeback_to_Fetch_3_p_dataaddr_sig_ec);
property writeback_to_Fetch_3_p_dataaddr_sig_ec;
  bit unsigned [7:0] dataaddr_sig_store; //Store the value of the output from the generated RTL
  writeback_to_Fetch_3_p_sequence
  ##1 (1'b1, dataaddr_sig_store = proc_states.dataaddr_sig)
  |->
  ##[0:1] (dataaddr_sig_store == dataAddr);
endproperty

writeback_to_Fetch_3_a_dataout_sig_ec: assert property (disable iff(reset) writeback_to_Fetch_3_p_dataout_sig_ec);
property writeback_to_Fetch_3_p_dataout_sig_ec;
  bit unsigned [7:0] dataout_sig_store; //Store the value of the output from the generated RTL
  writeback_to_Fetch_3_p_sequence
  ##1 (1'b1, dataout_sig_store = proc_states.dataout_sig)
  |->
  ##[0:1] (dataout_sig_store == dataOut);
endproperty

writeback_to_Fetch_3_a_instraddr_sig_ec: assert property (disable iff(reset) writeback_to_Fetch_3_p_instraddr_sig_ec);
property writeback_to_Fetch_3_p_instraddr_sig_ec;
  bit unsigned [15:0] instraddr_sig_store; //Store the value of the output from the generated RTL
  writeback_to_Fetch_3_p_sequence
  ##1 (1'b1, instraddr_sig_store = proc_states.instraddr_sig)
  |->
  ##[0:1] (instraddr_sig_store == instrAddr);
endproperty

writeback_to_Fetch_3_a_wen_sig_ec: assert property (disable iff(reset) writeback_to_Fetch_3_p_wen_sig_ec);
property writeback_to_Fetch_3_p_wen_sig_ec;
  bit wen_sig_store; //Store the value of the output from the generated RTL
  writeback_to_Fetch_3_p_sequence
  ##1 (1'b1, wen_sig_store = proc_states.wen_sig)
  |->
  ##[0:1] (wen_sig_store == writeEnable);
endproperty


endmodule
