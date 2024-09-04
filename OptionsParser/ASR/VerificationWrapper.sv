`include "OptionsParserRTL.sv"
`include "global_package.sv"
`include "OptionsParser_computational.sv"
`include "OptionsParser_control.sv"
`include "OptionsParser_operations.sv"
`include "OptionsParser.sv"

//Wrapper definition
module VerificationWrapper (
  input logic clk,
  input logic rst,
  input bit unsigned [7:0] fieldIn [14:0],
  input logic startParsing,
  output ParsedOptions parsed,
  output logic busy,
  output logic done,
  output logic ready,
  input logic read
);

//DUT instantiation
OptionsParserRTL dut_inst (
  .clk(clk),
  .rst(rst),
  .fieldIn(fieldIn),
  .startParsing(startParsing),
  .parsed(parsed),
  .busy(busy),
  .done(done),
  .ready(ready),
  .read(read)
);


//Generated RTL instantiation
OptionsParser OptionsParser (
  .rst(rst),
  .clk(clk),
  .fieldsIn_sig(fieldIn),
  .fieldsIn_sync(startParsing),
  .fieldsIn_notify(),
  .parsedOut_sig(),
  .parsedOut_sync(read),
  .parsedOut_notify()
);

default clocking default_clk @(posedge clk); endclocking

function bit xnr (input logic [31:0] sig, input logic [31:0] sig1);
  return &(~((sig | sig1) & (~sig | ~sig1)));
endfunction

sequence reset_sequence;
  rst ##1 !rst;
endsequence

sequence reset_p_sequence;
  reset_sequence;
endsequence

sequence DATAPARSING_to_DATAPARSING_p_sequence;
  (OptionsParser.OptionsParser_control_inst.current_state==3) &&
  !OptionsParser.OptionsParser_computational_inst.parsed.hasError &&
  !OptionsParser.OptionsParser_computational_inst.parsed.hasData &&
  ((OptionsParser.OptionsParser_computational_inst.counter < 4'd13) || (((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14]) == 0)) &&
  (OptionsParser.OptionsParser_computational_inst.CurrentState == (OptionsParser.OptionsParser_control_inst.current_state==3));
endsequence

sequence DATAPARSING_to_DATAPARSING_1_p_sequence;
  (OptionsParser.OptionsParser_control_inst.current_state==3) &&
  ((OptionsParser.OptionsParser_computational_inst.parsed.hasError || OptionsParser.OptionsParser_computational_inst.parsed.hasData) || !((OptionsParser.OptionsParser_computational_inst.counter < 4'd13) || (((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14]) == 0))) &&
  !((OptionsParser.OptionsParser_computational_inst.parsed.hasError || (OptionsParser.OptionsParser_computational_inst.counter > 4'd14)) || ((OptionsParser.OptionsParser_computational_inst.parsed.dataOptionLen.contents > 8'd5) && ((OptionsParser.OptionsParser_computational_inst.parsed.dataOptionLen.position + OptionsParser.OptionsParser_computational_inst.parsed.dataOptionLen.contents) > 9'd13))) &&
  OptionsParser.OptionsParser_computational_inst.parsed.hasData &&
  (OptionsParser.OptionsParser_computational_inst.counter <= (OptionsParser.OptionsParser_computational_inst.parsed.dataOptionLen.position + OptionsParser.OptionsParser_computational_inst.parsed.dataOptionLen.contents));
endsequence

sequence DATAPARSING_to_DATAPARSING_2_p_sequence;
  (OptionsParser.OptionsParser_control_inst.current_state==3) &&
  ((OptionsParser.OptionsParser_computational_inst.parsed.hasError || OptionsParser.OptionsParser_computational_inst.parsed.hasData) || !((OptionsParser.OptionsParser_computational_inst.counter < 4'd13) || (((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14]) == 0))) &&
  !((OptionsParser.OptionsParser_computational_inst.parsed.hasError || (OptionsParser.OptionsParser_computational_inst.counter > 4'd14)) || ((OptionsParser.OptionsParser_computational_inst.parsed.dataOptionLen.contents > 8'd5) && ((OptionsParser.OptionsParser_computational_inst.parsed.dataOptionLen.position + OptionsParser.OptionsParser_computational_inst.parsed.dataOptionLen.contents) > 9'd13))) &&
  !(OptionsParser.OptionsParser_computational_inst.parsed.hasData && (OptionsParser.OptionsParser_computational_inst.counter <= (OptionsParser.OptionsParser_computational_inst.parsed.dataOptionLen.position + OptionsParser.OptionsParser_computational_inst.parsed.dataOptionLen.contents))) &&
  (((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) != 2) &&
  ((((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) != 3) || OptionsParser.OptionsParser_computational_inst.parsed.hasInfo) &&
  (OptionsParser.OptionsParser_computational_inst.CurrentState == (OptionsParser.OptionsParser_control_inst.current_state==3));
endsequence

sequence DATAPARSING_to_DONE_p_sequence;
  (OptionsParser.OptionsParser_control_inst.current_state==3) &&
  ((OptionsParser.OptionsParser_computational_inst.parsed.hasError || OptionsParser.OptionsParser_computational_inst.parsed.hasData) || !((OptionsParser.OptionsParser_computational_inst.counter < 4'd13) || (((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14]) == 0))) &&
  ((OptionsParser.OptionsParser_computational_inst.parsed.hasError || (OptionsParser.OptionsParser_computational_inst.counter > 4'd14)) || ((OptionsParser.OptionsParser_computational_inst.parsed.dataOptionLen.contents > 8'd5) && ((OptionsParser.OptionsParser_computational_inst.parsed.dataOptionLen.position + OptionsParser.OptionsParser_computational_inst.parsed.dataOptionLen.contents) > 9'd13)));
endsequence

sequence DATAPARSING_to_ENDPARSING_p_sequence;
  (OptionsParser.OptionsParser_control_inst.current_state==3) &&
  ((OptionsParser.OptionsParser_computational_inst.parsed.hasError || OptionsParser.OptionsParser_computational_inst.parsed.hasData) || !((OptionsParser.OptionsParser_computational_inst.counter < 4'd13) || (((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14]) == 0))) &&
  !((OptionsParser.OptionsParser_computational_inst.parsed.hasError || (OptionsParser.OptionsParser_computational_inst.counter > 4'd14)) || ((OptionsParser.OptionsParser_computational_inst.parsed.dataOptionLen.contents > 8'd5) && ((OptionsParser.OptionsParser_computational_inst.parsed.dataOptionLen.position + OptionsParser.OptionsParser_computational_inst.parsed.dataOptionLen.contents) > 9'd13))) &&
  !(OptionsParser.OptionsParser_computational_inst.parsed.hasData && (OptionsParser.OptionsParser_computational_inst.counter <= (OptionsParser.OptionsParser_computational_inst.parsed.dataOptionLen.position + OptionsParser.OptionsParser_computational_inst.parsed.dataOptionLen.contents))) &&
  (((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) == 2);
endsequence

sequence DATAPARSING_to_INFOPARSING_p_sequence;
  (OptionsParser.OptionsParser_control_inst.current_state==3) &&
  ((OptionsParser.OptionsParser_computational_inst.parsed.hasError || OptionsParser.OptionsParser_computational_inst.parsed.hasData) || !((OptionsParser.OptionsParser_computational_inst.counter < 4'd13) || (((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14]) == 0))) &&
  !((OptionsParser.OptionsParser_computational_inst.parsed.hasError || (OptionsParser.OptionsParser_computational_inst.counter > 4'd14)) || ((OptionsParser.OptionsParser_computational_inst.parsed.dataOptionLen.contents > 8'd5) && ((OptionsParser.OptionsParser_computational_inst.parsed.dataOptionLen.position + OptionsParser.OptionsParser_computational_inst.parsed.dataOptionLen.contents) > 9'd13))) &&
  !(OptionsParser.OptionsParser_computational_inst.parsed.hasData && (OptionsParser.OptionsParser_computational_inst.counter <= (OptionsParser.OptionsParser_computational_inst.parsed.dataOptionLen.position + OptionsParser.OptionsParser_computational_inst.parsed.dataOptionLen.contents))) &&
  (((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) != 2) &&
  (((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) == 3) &&
  !OptionsParser.OptionsParser_computational_inst.parsed.hasInfo;
endsequence

sequence DONE_to_READY_p_sequence;
  (OptionsParser.OptionsParser_control_inst.current_state==5) &&
  OptionsParser.parsedOut_sync;
endsequence

sequence ENDPARSING_to_DONE_p_sequence;
  (OptionsParser.OptionsParser_control_inst.current_state==4);
endsequence

sequence INFOPARSING_to_DATAPARSING_p_sequence;
  (OptionsParser.OptionsParser_control_inst.current_state==2) &&
  (OptionsParser.OptionsParser_computational_inst.parsed.hasInfo || (OptionsParser.OptionsParser_computational_inst.counter >= 4'd13)) &&
  (OptionsParser.OptionsParser_computational_inst.counter <= 4'd14) &&
  (((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))) != 2) &&
  (((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : OptionsParser.OptionsParser_computational_inst.fields [11]))))))))))) == 4) &&
  !OptionsParser.OptionsParser_computational_inst.parsed.hasData &&
  (OptionsParser.OptionsParser_computational_inst.counter < 4'd12) &&
  (((((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) > 8'd5) || ((((((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) + OptionsParser.OptionsParser_computational_inst.counter) + 9'd1) > 10'd13));
endsequence

sequence INFOPARSING_to_DATAPARSING_1_p_sequence;
  (OptionsParser.OptionsParser_control_inst.current_state==2) &&
  (OptionsParser.OptionsParser_computational_inst.parsed.hasInfo || (OptionsParser.OptionsParser_computational_inst.counter >= 4'd13)) &&
  (OptionsParser.OptionsParser_computational_inst.counter <= 4'd14) &&
  (((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))) != 2) &&
  (((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : OptionsParser.OptionsParser_computational_inst.fields [11]))))))))))) == 4) &&
  !OptionsParser.OptionsParser_computational_inst.parsed.hasData &&
  (OptionsParser.OptionsParser_computational_inst.counter < 4'd12) &&
  !(((((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) > 8'd5) || ((((((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) + OptionsParser.OptionsParser_computational_inst.counter) + 9'd1) > 10'd13));
endsequence

sequence INFOPARSING_to_DONE_p_sequence;
  (OptionsParser.OptionsParser_control_inst.current_state==2) &&
  (OptionsParser.OptionsParser_computational_inst.parsed.hasInfo || (OptionsParser.OptionsParser_computational_inst.counter >= 4'd13)) &&
  (OptionsParser.OptionsParser_computational_inst.counter > 4'd14);
endsequence

sequence INFOPARSING_to_ENDPARSING_p_sequence;
  (OptionsParser.OptionsParser_control_inst.current_state==2) &&
  (OptionsParser.OptionsParser_computational_inst.parsed.hasInfo || (OptionsParser.OptionsParser_computational_inst.counter >= 4'd13)) &&
  (OptionsParser.OptionsParser_computational_inst.counter <= 4'd14) &&
  (((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) == 2);
endsequence

sequence INFOPARSING_to_INFOPARSING_p_sequence;
  (OptionsParser.OptionsParser_control_inst.current_state==2) &&
  !OptionsParser.OptionsParser_computational_inst.parsed.hasInfo &&
  (OptionsParser.OptionsParser_computational_inst.counter < 4'd13) &&
  (OptionsParser.OptionsParser_computational_inst.CurrentState == (OptionsParser.OptionsParser_control_inst.current_state==2));
endsequence

sequence INFOPARSING_to_INFOPARSING_1_p_sequence;
  (OptionsParser.OptionsParser_control_inst.current_state==2) &&
  (OptionsParser.OptionsParser_computational_inst.parsed.hasInfo || (OptionsParser.OptionsParser_computational_inst.counter >= 4'd13)) &&
  (OptionsParser.OptionsParser_computational_inst.counter <= 4'd14) &&
  (((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) != 2) &&
  !(((((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : OptionsParser.OptionsParser_computational_inst.fields [11]))))))))))) == 4) && !OptionsParser.OptionsParser_computational_inst.parsed.hasData) && (OptionsParser.OptionsParser_computational_inst.counter < 4'd12));
endsequence

sequence READY_to_STARTPARSING_p_sequence;
  (OptionsParser.OptionsParser_control_inst.current_state==0) &&
  OptionsParser.fieldsIn_sync;
endsequence

sequence STARTPARSING_to_DATAPARSING_p_sequence;
  (OptionsParser.OptionsParser_control_inst.current_state==1) &&
  (OptionsParser.OptionsParser_computational_inst.counter <= 4'd14) &&
  !((((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))) == 2) && OptionsParser.OptionsParser_computational_inst.parsed.hasStart) &&
  !((((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))) == 3) && OptionsParser.OptionsParser_computational_inst.parsed.hasStart) &&
  (((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : OptionsParser.OptionsParser_computational_inst.fields [11]))))))))))) == 4) &&
  OptionsParser.OptionsParser_computational_inst.parsed.hasStart &&
  (OptionsParser.OptionsParser_computational_inst.counter < 4'd12) &&
  (((((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) > 8'd5) || ((((((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) + OptionsParser.OptionsParser_computational_inst.counter) + 9'd1) > 10'd13));
endsequence

sequence STARTPARSING_to_DATAPARSING_1_p_sequence;
  (OptionsParser.OptionsParser_control_inst.current_state==1) &&
  (OptionsParser.OptionsParser_computational_inst.counter <= 4'd14) &&
  !((((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))) == 2) && OptionsParser.OptionsParser_computational_inst.parsed.hasStart) &&
  !((((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))) == 3) && OptionsParser.OptionsParser_computational_inst.parsed.hasStart) &&
  (((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : OptionsParser.OptionsParser_computational_inst.fields [11]))))))))))) == 4) &&
  OptionsParser.OptionsParser_computational_inst.parsed.hasStart &&
  (OptionsParser.OptionsParser_computational_inst.counter < 4'd12) &&
  !(((((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) > 8'd5) || ((((((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) + OptionsParser.OptionsParser_computational_inst.counter) + 9'd1) > 10'd13));
endsequence

sequence STARTPARSING_to_DONE_p_sequence;
  (OptionsParser.OptionsParser_control_inst.current_state==1) &&
  (OptionsParser.OptionsParser_computational_inst.counter > 4'd14);
endsequence

sequence STARTPARSING_to_ENDPARSING_p_sequence;
  (OptionsParser.OptionsParser_control_inst.current_state==1) &&
  (OptionsParser.OptionsParser_computational_inst.counter <= 4'd14) &&
  (((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) == 2) &&
  OptionsParser.OptionsParser_computational_inst.parsed.hasStart;
endsequence

sequence STARTPARSING_to_INFOPARSING_p_sequence;
  (OptionsParser.OptionsParser_control_inst.current_state==1) &&
  (OptionsParser.OptionsParser_computational_inst.counter <= 4'd14) &&
  !((((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) == 2) && OptionsParser.OptionsParser_computational_inst.parsed.hasStart) &&
  (((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) == 3) &&
  OptionsParser.OptionsParser_computational_inst.parsed.hasStart;
endsequence

sequence STARTPARSING_to_STARTPARSING_p_sequence;
  (OptionsParser.OptionsParser_control_inst.current_state==1) &&
  (OptionsParser.OptionsParser_computational_inst.counter <= 4'd14) &&
  !((((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) == 2) && OptionsParser.OptionsParser_computational_inst.parsed.hasStart) &&
  !((((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) == 3) && OptionsParser.OptionsParser_computational_inst.parsed.hasStart) &&
  !(((((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : OptionsParser.OptionsParser_computational_inst.fields [11]))))))))))) == 4) && OptionsParser.OptionsParser_computational_inst.parsed.hasStart) && (OptionsParser.OptionsParser_computational_inst.counter < 4'd12));
endsequence

sequence DONE_wait_p_sequence;
  (OptionsParser.OptionsParser_control_inst.current_state==5) &&
  !OptionsParser.parsedOut_sync;
endsequence

sequence READY_wait_p_sequence;
  (OptionsParser.OptionsParser_control_inst.current_state==0) &&
  !OptionsParser.fieldsIn_sync;
endsequence

//Smart states refiner properties

//RefinementVector binding
logic [17:0] RefinementVector;
assign RefinementVector[0] = dut_inst.startParsing;
assign RefinementVector[1] = dut_inst.parsed.hasStart;
assign RefinementVector[2] = dut_inst.parsed.hasInfo;
assign RefinementVector[3] = dut_inst.parsed.hasData;
assign RefinementVector[4] = dut_inst.parsed.hasEnd;
assign RefinementVector[5] = dut_inst.parsed.isEmpty;
assign RefinementVector[6] = dut_inst.parsed.hasError;
assign RefinementVector[7] = dut_inst.busy;
assign RefinementVector[8] = dut_inst.done;
assign RefinementVector[9] = dut_inst.ready;
assign RefinementVector[10] = dut_inst.read;
assign RefinementVector[11] = dut_inst.dataFlag;
assign RefinementVector[12] = dut_inst.dataLenFlag;
assign RefinementVector[13] = dut_inst.InfoFlag;
assign RefinementVector[14] = dut_inst.dataDone;
assign RefinementVector[17:15] = dut_inst.state_s;


//Bit blasting properties

/*********************************************/
/* DATAPARSING state bit-blasting properties */
/*********************************************/

//DATAPARSING_to_DATAPARSING_p_sequence
for(genvar bitNum = 0; bitNum < 18 ; bitNum++) begin: DATAPARSING__blasting__DATAPARSING_to_DATAPARSING_p_sequence_gen
 DATAPARSING__blasting__DATAPARSING_to_DATAPARSING_p_sequence_a: assert property (disable iff(rst)DATAPARSING__blasting__DATAPARSING_to_DATAPARSING_p_sequence(bitNum));
 DATAPARSING__blasting__DATAPARSING_to_DATAPARSING_p_sequence_NOT_a: assert property (disable iff(rst)DATAPARSING__blasting__DATAPARSING_to_DATAPARSING_p_sequence_NOT(bitNum));
end

property DATAPARSING__blasting__DATAPARSING_to_DATAPARSING_p_sequence(bitPos);
 DATAPARSING_to_DATAPARSING_p_sequence
|->
 ##1 RefinementVector[bitPos];
endproperty

property DATAPARSING__blasting__DATAPARSING_to_DATAPARSING_p_sequence_NOT(bitPos);
 DATAPARSING_to_DATAPARSING_p_sequence
|->
 ##1 !RefinementVector[bitPos];
endproperty

//DATAPARSING_to_DATAPARSING_1_p_sequence
for(genvar bitNum = 0; bitNum < 18 ; bitNum++) begin: DATAPARSING__blasting__DATAPARSING_to_DATAPARSING_1_p_sequence_gen
 DATAPARSING__blasting__DATAPARSING_to_DATAPARSING_1_p_sequence_a: assert property (disable iff(rst)DATAPARSING__blasting__DATAPARSING_to_DATAPARSING_1_p_sequence(bitNum));
 DATAPARSING__blasting__DATAPARSING_to_DATAPARSING_1_p_sequence_NOT_a: assert property (disable iff(rst)DATAPARSING__blasting__DATAPARSING_to_DATAPARSING_1_p_sequence_NOT(bitNum));
end

property DATAPARSING__blasting__DATAPARSING_to_DATAPARSING_1_p_sequence(bitPos);
 DATAPARSING_to_DATAPARSING_1_p_sequence
|->
 ##1 RefinementVector[bitPos];
endproperty

property DATAPARSING__blasting__DATAPARSING_to_DATAPARSING_1_p_sequence_NOT(bitPos);
 DATAPARSING_to_DATAPARSING_1_p_sequence
|->
 ##1 !RefinementVector[bitPos];
endproperty

//DATAPARSING_to_DATAPARSING_2_p_sequence
for(genvar bitNum = 0; bitNum < 18 ; bitNum++) begin: DATAPARSING__blasting__DATAPARSING_to_DATAPARSING_2_p_sequence_gen
 DATAPARSING__blasting__DATAPARSING_to_DATAPARSING_2_p_sequence_a: assert property (disable iff(rst)DATAPARSING__blasting__DATAPARSING_to_DATAPARSING_2_p_sequence(bitNum));
 DATAPARSING__blasting__DATAPARSING_to_DATAPARSING_2_p_sequence_NOT_a: assert property (disable iff(rst)DATAPARSING__blasting__DATAPARSING_to_DATAPARSING_2_p_sequence_NOT(bitNum));
end

property DATAPARSING__blasting__DATAPARSING_to_DATAPARSING_2_p_sequence(bitPos);
 DATAPARSING_to_DATAPARSING_2_p_sequence
|->
 ##1 RefinementVector[bitPos];
endproperty

property DATAPARSING__blasting__DATAPARSING_to_DATAPARSING_2_p_sequence_NOT(bitPos);
 DATAPARSING_to_DATAPARSING_2_p_sequence
|->
 ##1 !RefinementVector[bitPos];
endproperty

//INFOPARSING_to_DATAPARSING_p_sequence
for(genvar bitNum = 0; bitNum < 18 ; bitNum++) begin: DATAPARSING__blasting__INFOPARSING_to_DATAPARSING_p_sequence_gen
 DATAPARSING__blasting__INFOPARSING_to_DATAPARSING_p_sequence_a: assert property (disable iff(rst)DATAPARSING__blasting__INFOPARSING_to_DATAPARSING_p_sequence(bitNum));
 DATAPARSING__blasting__INFOPARSING_to_DATAPARSING_p_sequence_NOT_a: assert property (disable iff(rst)DATAPARSING__blasting__INFOPARSING_to_DATAPARSING_p_sequence_NOT(bitNum));
end

property DATAPARSING__blasting__INFOPARSING_to_DATAPARSING_p_sequence(bitPos);
 INFOPARSING_to_DATAPARSING_p_sequence
|->
 ##1 RefinementVector[bitPos];
endproperty

property DATAPARSING__blasting__INFOPARSING_to_DATAPARSING_p_sequence_NOT(bitPos);
 INFOPARSING_to_DATAPARSING_p_sequence
|->
 ##1 !RefinementVector[bitPos];
endproperty

//INFOPARSING_to_DATAPARSING_1_p_sequence
for(genvar bitNum = 0; bitNum < 18 ; bitNum++) begin: DATAPARSING__blasting__INFOPARSING_to_DATAPARSING_1_p_sequence_gen
 DATAPARSING__blasting__INFOPARSING_to_DATAPARSING_1_p_sequence_a: assert property (disable iff(rst)DATAPARSING__blasting__INFOPARSING_to_DATAPARSING_1_p_sequence(bitNum));
 DATAPARSING__blasting__INFOPARSING_to_DATAPARSING_1_p_sequence_NOT_a: assert property (disable iff(rst)DATAPARSING__blasting__INFOPARSING_to_DATAPARSING_1_p_sequence_NOT(bitNum));
end

property DATAPARSING__blasting__INFOPARSING_to_DATAPARSING_1_p_sequence(bitPos);
 INFOPARSING_to_DATAPARSING_1_p_sequence
|->
 ##1 RefinementVector[bitPos];
endproperty

property DATAPARSING__blasting__INFOPARSING_to_DATAPARSING_1_p_sequence_NOT(bitPos);
 INFOPARSING_to_DATAPARSING_1_p_sequence
|->
 ##1 !RefinementVector[bitPos];
endproperty

//STARTPARSING_to_DATAPARSING_p_sequence
for(genvar bitNum = 0; bitNum < 18 ; bitNum++) begin: DATAPARSING__blasting__STARTPARSING_to_DATAPARSING_p_sequence_gen
 DATAPARSING__blasting__STARTPARSING_to_DATAPARSING_p_sequence_a: assert property (disable iff(rst)DATAPARSING__blasting__STARTPARSING_to_DATAPARSING_p_sequence(bitNum));
 DATAPARSING__blasting__STARTPARSING_to_DATAPARSING_p_sequence_NOT_a: assert property (disable iff(rst)DATAPARSING__blasting__STARTPARSING_to_DATAPARSING_p_sequence_NOT(bitNum));
end

property DATAPARSING__blasting__STARTPARSING_to_DATAPARSING_p_sequence(bitPos);
 STARTPARSING_to_DATAPARSING_p_sequence
|->
 ##1 RefinementVector[bitPos];
endproperty

property DATAPARSING__blasting__STARTPARSING_to_DATAPARSING_p_sequence_NOT(bitPos);
 STARTPARSING_to_DATAPARSING_p_sequence
|->
 ##1 !RefinementVector[bitPos];
endproperty

//STARTPARSING_to_DATAPARSING_1_p_sequence
for(genvar bitNum = 0; bitNum < 18 ; bitNum++) begin: DATAPARSING__blasting__STARTPARSING_to_DATAPARSING_1_p_sequence_gen
 DATAPARSING__blasting__STARTPARSING_to_DATAPARSING_1_p_sequence_a: assert property (disable iff(rst)DATAPARSING__blasting__STARTPARSING_to_DATAPARSING_1_p_sequence(bitNum));
 DATAPARSING__blasting__STARTPARSING_to_DATAPARSING_1_p_sequence_NOT_a: assert property (disable iff(rst)DATAPARSING__blasting__STARTPARSING_to_DATAPARSING_1_p_sequence_NOT(bitNum));
end

property DATAPARSING__blasting__STARTPARSING_to_DATAPARSING_1_p_sequence(bitPos);
 STARTPARSING_to_DATAPARSING_1_p_sequence
|->
 ##1 RefinementVector[bitPos];
endproperty

property DATAPARSING__blasting__STARTPARSING_to_DATAPARSING_1_p_sequence_NOT(bitPos);
 STARTPARSING_to_DATAPARSING_1_p_sequence
|->
 ##1 !RefinementVector[bitPos];
endproperty


/**************************************/
/* DONE state bit-blasting properties */
/**************************************/

//DATAPARSING_to_DONE_p_sequence
for(genvar bitNum = 0; bitNum < 18 ; bitNum++) begin: DONE__blasting__DATAPARSING_to_DONE_p_sequence_gen
 DONE__blasting__DATAPARSING_to_DONE_p_sequence_a: assert property (disable iff(rst)DONE__blasting__DATAPARSING_to_DONE_p_sequence(bitNum));
 DONE__blasting__DATAPARSING_to_DONE_p_sequence_NOT_a: assert property (disable iff(rst)DONE__blasting__DATAPARSING_to_DONE_p_sequence_NOT(bitNum));
end

property DONE__blasting__DATAPARSING_to_DONE_p_sequence(bitPos);
 DATAPARSING_to_DONE_p_sequence
|->
 ##1 RefinementVector[bitPos];
endproperty

property DONE__blasting__DATAPARSING_to_DONE_p_sequence_NOT(bitPos);
 DATAPARSING_to_DONE_p_sequence
|->
 ##1 !RefinementVector[bitPos];
endproperty

//ENDPARSING_to_DONE_p_sequence
for(genvar bitNum = 0; bitNum < 18 ; bitNum++) begin: DONE__blasting__ENDPARSING_to_DONE_p_sequence_gen
 DONE__blasting__ENDPARSING_to_DONE_p_sequence_a: assert property (disable iff(rst)DONE__blasting__ENDPARSING_to_DONE_p_sequence(bitNum));
 DONE__blasting__ENDPARSING_to_DONE_p_sequence_NOT_a: assert property (disable iff(rst)DONE__blasting__ENDPARSING_to_DONE_p_sequence_NOT(bitNum));
end

property DONE__blasting__ENDPARSING_to_DONE_p_sequence(bitPos);
 ENDPARSING_to_DONE_p_sequence
|->
 ##1 RefinementVector[bitPos];
endproperty

property DONE__blasting__ENDPARSING_to_DONE_p_sequence_NOT(bitPos);
 ENDPARSING_to_DONE_p_sequence
|->
 ##1 !RefinementVector[bitPos];
endproperty

//INFOPARSING_to_DONE_p_sequence
for(genvar bitNum = 0; bitNum < 18 ; bitNum++) begin: DONE__blasting__INFOPARSING_to_DONE_p_sequence_gen
 DONE__blasting__INFOPARSING_to_DONE_p_sequence_a: assert property (disable iff(rst)DONE__blasting__INFOPARSING_to_DONE_p_sequence(bitNum));
 DONE__blasting__INFOPARSING_to_DONE_p_sequence_NOT_a: assert property (disable iff(rst)DONE__blasting__INFOPARSING_to_DONE_p_sequence_NOT(bitNum));
end

property DONE__blasting__INFOPARSING_to_DONE_p_sequence(bitPos);
 INFOPARSING_to_DONE_p_sequence
|->
 ##1 RefinementVector[bitPos];
endproperty

property DONE__blasting__INFOPARSING_to_DONE_p_sequence_NOT(bitPos);
 INFOPARSING_to_DONE_p_sequence
|->
 ##1 !RefinementVector[bitPos];
endproperty

//STARTPARSING_to_DONE_p_sequence
for(genvar bitNum = 0; bitNum < 18 ; bitNum++) begin: DONE__blasting__STARTPARSING_to_DONE_p_sequence_gen
 DONE__blasting__STARTPARSING_to_DONE_p_sequence_a: assert property (disable iff(rst)DONE__blasting__STARTPARSING_to_DONE_p_sequence(bitNum));
 DONE__blasting__STARTPARSING_to_DONE_p_sequence_NOT_a: assert property (disable iff(rst)DONE__blasting__STARTPARSING_to_DONE_p_sequence_NOT(bitNum));
end

property DONE__blasting__STARTPARSING_to_DONE_p_sequence(bitPos);
 STARTPARSING_to_DONE_p_sequence
|->
 ##1 RefinementVector[bitPos];
endproperty

property DONE__blasting__STARTPARSING_to_DONE_p_sequence_NOT(bitPos);
 STARTPARSING_to_DONE_p_sequence
|->
 ##1 !RefinementVector[bitPos];
endproperty

//DONE_wait_p_sequence
for(genvar bitNum = 0; bitNum < 18 ; bitNum++) begin: DONE__blasting__DONE_wait_p_sequence_gen
 DONE__blasting__DONE_wait_p_sequence_a: assert property (disable iff(rst)DONE__blasting__DONE_wait_p_sequence(bitNum));
 DONE__blasting__DONE_wait_p_sequence_NOT_a: assert property (disable iff(rst)DONE__blasting__DONE_wait_p_sequence_NOT(bitNum));
end

property DONE__blasting__DONE_wait_p_sequence(bitPos);
 DONE_wait_p_sequence
|->
 ##1 RefinementVector[bitPos];
endproperty

property DONE__blasting__DONE_wait_p_sequence_NOT(bitPos);
 DONE_wait_p_sequence
|->
 ##1 !RefinementVector[bitPos];
endproperty


/********************************************/
/* ENDPARSING state bit-blasting properties */
/********************************************/

//DATAPARSING_to_ENDPARSING_p_sequence
for(genvar bitNum = 0; bitNum < 18 ; bitNum++) begin: ENDPARSING__blasting__DATAPARSING_to_ENDPARSING_p_sequence_gen
 ENDPARSING__blasting__DATAPARSING_to_ENDPARSING_p_sequence_a: assert property (disable iff(rst)ENDPARSING__blasting__DATAPARSING_to_ENDPARSING_p_sequence(bitNum));
 ENDPARSING__blasting__DATAPARSING_to_ENDPARSING_p_sequence_NOT_a: assert property (disable iff(rst)ENDPARSING__blasting__DATAPARSING_to_ENDPARSING_p_sequence_NOT(bitNum));
end

property ENDPARSING__blasting__DATAPARSING_to_ENDPARSING_p_sequence(bitPos);
 DATAPARSING_to_ENDPARSING_p_sequence
|->
 ##1 RefinementVector[bitPos];
endproperty

property ENDPARSING__blasting__DATAPARSING_to_ENDPARSING_p_sequence_NOT(bitPos);
 DATAPARSING_to_ENDPARSING_p_sequence
|->
 ##1 !RefinementVector[bitPos];
endproperty

//INFOPARSING_to_ENDPARSING_p_sequence
for(genvar bitNum = 0; bitNum < 18 ; bitNum++) begin: ENDPARSING__blasting__INFOPARSING_to_ENDPARSING_p_sequence_gen
 ENDPARSING__blasting__INFOPARSING_to_ENDPARSING_p_sequence_a: assert property (disable iff(rst)ENDPARSING__blasting__INFOPARSING_to_ENDPARSING_p_sequence(bitNum));
 ENDPARSING__blasting__INFOPARSING_to_ENDPARSING_p_sequence_NOT_a: assert property (disable iff(rst)ENDPARSING__blasting__INFOPARSING_to_ENDPARSING_p_sequence_NOT(bitNum));
end

property ENDPARSING__blasting__INFOPARSING_to_ENDPARSING_p_sequence(bitPos);
 INFOPARSING_to_ENDPARSING_p_sequence
|->
 ##1 RefinementVector[bitPos];
endproperty

property ENDPARSING__blasting__INFOPARSING_to_ENDPARSING_p_sequence_NOT(bitPos);
 INFOPARSING_to_ENDPARSING_p_sequence
|->
 ##1 !RefinementVector[bitPos];
endproperty

//STARTPARSING_to_ENDPARSING_p_sequence
for(genvar bitNum = 0; bitNum < 18 ; bitNum++) begin: ENDPARSING__blasting__STARTPARSING_to_ENDPARSING_p_sequence_gen
 ENDPARSING__blasting__STARTPARSING_to_ENDPARSING_p_sequence_a: assert property (disable iff(rst)ENDPARSING__blasting__STARTPARSING_to_ENDPARSING_p_sequence(bitNum));
 ENDPARSING__blasting__STARTPARSING_to_ENDPARSING_p_sequence_NOT_a: assert property (disable iff(rst)ENDPARSING__blasting__STARTPARSING_to_ENDPARSING_p_sequence_NOT(bitNum));
end

property ENDPARSING__blasting__STARTPARSING_to_ENDPARSING_p_sequence(bitPos);
 STARTPARSING_to_ENDPARSING_p_sequence
|->
 ##1 RefinementVector[bitPos];
endproperty

property ENDPARSING__blasting__STARTPARSING_to_ENDPARSING_p_sequence_NOT(bitPos);
 STARTPARSING_to_ENDPARSING_p_sequence
|->
 ##1 !RefinementVector[bitPos];
endproperty


/*********************************************/
/* INFOPARSING state bit-blasting properties */
/*********************************************/

//DATAPARSING_to_INFOPARSING_p_sequence
for(genvar bitNum = 0; bitNum < 18 ; bitNum++) begin: INFOPARSING__blasting__DATAPARSING_to_INFOPARSING_p_sequence_gen
 INFOPARSING__blasting__DATAPARSING_to_INFOPARSING_p_sequence_a: assert property (disable iff(rst)INFOPARSING__blasting__DATAPARSING_to_INFOPARSING_p_sequence(bitNum));
 INFOPARSING__blasting__DATAPARSING_to_INFOPARSING_p_sequence_NOT_a: assert property (disable iff(rst)INFOPARSING__blasting__DATAPARSING_to_INFOPARSING_p_sequence_NOT(bitNum));
end

property INFOPARSING__blasting__DATAPARSING_to_INFOPARSING_p_sequence(bitPos);
 DATAPARSING_to_INFOPARSING_p_sequence
|->
 ##1 RefinementVector[bitPos];
endproperty

property INFOPARSING__blasting__DATAPARSING_to_INFOPARSING_p_sequence_NOT(bitPos);
 DATAPARSING_to_INFOPARSING_p_sequence
|->
 ##1 !RefinementVector[bitPos];
endproperty

//INFOPARSING_to_INFOPARSING_p_sequence
for(genvar bitNum = 0; bitNum < 18 ; bitNum++) begin: INFOPARSING__blasting__INFOPARSING_to_INFOPARSING_p_sequence_gen
 INFOPARSING__blasting__INFOPARSING_to_INFOPARSING_p_sequence_a: assert property (disable iff(rst)INFOPARSING__blasting__INFOPARSING_to_INFOPARSING_p_sequence(bitNum));
 INFOPARSING__blasting__INFOPARSING_to_INFOPARSING_p_sequence_NOT_a: assert property (disable iff(rst)INFOPARSING__blasting__INFOPARSING_to_INFOPARSING_p_sequence_NOT(bitNum));
end

property INFOPARSING__blasting__INFOPARSING_to_INFOPARSING_p_sequence(bitPos);
 INFOPARSING_to_INFOPARSING_p_sequence
|->
 ##1 RefinementVector[bitPos];
endproperty

property INFOPARSING__blasting__INFOPARSING_to_INFOPARSING_p_sequence_NOT(bitPos);
 INFOPARSING_to_INFOPARSING_p_sequence
|->
 ##1 !RefinementVector[bitPos];
endproperty

//INFOPARSING_to_INFOPARSING_1_p_sequence
for(genvar bitNum = 0; bitNum < 18 ; bitNum++) begin: INFOPARSING__blasting__INFOPARSING_to_INFOPARSING_1_p_sequence_gen
 INFOPARSING__blasting__INFOPARSING_to_INFOPARSING_1_p_sequence_a: assert property (disable iff(rst)INFOPARSING__blasting__INFOPARSING_to_INFOPARSING_1_p_sequence(bitNum));
 INFOPARSING__blasting__INFOPARSING_to_INFOPARSING_1_p_sequence_NOT_a: assert property (disable iff(rst)INFOPARSING__blasting__INFOPARSING_to_INFOPARSING_1_p_sequence_NOT(bitNum));
end

property INFOPARSING__blasting__INFOPARSING_to_INFOPARSING_1_p_sequence(bitPos);
 INFOPARSING_to_INFOPARSING_1_p_sequence
|->
 ##1 RefinementVector[bitPos];
endproperty

property INFOPARSING__blasting__INFOPARSING_to_INFOPARSING_1_p_sequence_NOT(bitPos);
 INFOPARSING_to_INFOPARSING_1_p_sequence
|->
 ##1 !RefinementVector[bitPos];
endproperty

//STARTPARSING_to_INFOPARSING_p_sequence
for(genvar bitNum = 0; bitNum < 18 ; bitNum++) begin: INFOPARSING__blasting__STARTPARSING_to_INFOPARSING_p_sequence_gen
 INFOPARSING__blasting__STARTPARSING_to_INFOPARSING_p_sequence_a: assert property (disable iff(rst)INFOPARSING__blasting__STARTPARSING_to_INFOPARSING_p_sequence(bitNum));
 INFOPARSING__blasting__STARTPARSING_to_INFOPARSING_p_sequence_NOT_a: assert property (disable iff(rst)INFOPARSING__blasting__STARTPARSING_to_INFOPARSING_p_sequence_NOT(bitNum));
end

property INFOPARSING__blasting__STARTPARSING_to_INFOPARSING_p_sequence(bitPos);
 STARTPARSING_to_INFOPARSING_p_sequence
|->
 ##1 RefinementVector[bitPos];
endproperty

property INFOPARSING__blasting__STARTPARSING_to_INFOPARSING_p_sequence_NOT(bitPos);
 STARTPARSING_to_INFOPARSING_p_sequence
|->
 ##1 !RefinementVector[bitPos];
endproperty


/***************************************/
/* READY state bit-blasting properties */
/***************************************/

//DONE_to_READY_p_sequence
for(genvar bitNum = 0; bitNum < 18 ; bitNum++) begin: READY__blasting__DONE_to_READY_p_sequence_gen
 READY__blasting__DONE_to_READY_p_sequence_a: assert property (disable iff(rst)READY__blasting__DONE_to_READY_p_sequence(bitNum));
 READY__blasting__DONE_to_READY_p_sequence_NOT_a: assert property (disable iff(rst)READY__blasting__DONE_to_READY_p_sequence_NOT(bitNum));
end

property READY__blasting__DONE_to_READY_p_sequence(bitPos);
 DONE_to_READY_p_sequence
|->
 ##1 RefinementVector[bitPos];
endproperty

property READY__blasting__DONE_to_READY_p_sequence_NOT(bitPos);
 DONE_to_READY_p_sequence
|->
 ##1 !RefinementVector[bitPos];
endproperty

//READY_wait_p_sequence
for(genvar bitNum = 0; bitNum < 18 ; bitNum++) begin: READY__blasting__READY_wait_p_sequence_gen
 READY__blasting__READY_wait_p_sequence_a: assert property (disable iff(rst)READY__blasting__READY_wait_p_sequence(bitNum));
 READY__blasting__READY_wait_p_sequence_NOT_a: assert property (disable iff(rst)READY__blasting__READY_wait_p_sequence_NOT(bitNum));
end

property READY__blasting__READY_wait_p_sequence(bitPos);
 READY_wait_p_sequence
|->
 ##1 RefinementVector[bitPos];
endproperty

property READY__blasting__READY_wait_p_sequence_NOT(bitPos);
 READY_wait_p_sequence
|->
 ##1 !RefinementVector[bitPos];
endproperty

//reset_p_sequence
for(genvar bitNum = 0; bitNum < 18 ; bitNum++) begin: READY__blasting__reset_p_sequence_gen
 READY__blasting__reset_p_sequence_a: assert property (READY__blasting__reset_p_sequence(bitNum));
 READY__blasting__reset_p_sequence_NOT_a: assert property (READY__blasting__reset_p_sequence_NOT(bitNum));
end

property READY__blasting__reset_p_sequence(bitPos);
 reset_p_sequence
|->
 RefinementVector[bitPos];
endproperty

property READY__blasting__reset_p_sequence_NOT(bitPos);
 reset_p_sequence
|->
 !RefinementVector[bitPos];
endproperty


/**********************************************/
/* STARTPARSING state bit-blasting properties */
/**********************************************/

//READY_to_STARTPARSING_p_sequence
for(genvar bitNum = 0; bitNum < 18 ; bitNum++) begin: STARTPARSING__blasting__READY_to_STARTPARSING_p_sequence_gen
 STARTPARSING__blasting__READY_to_STARTPARSING_p_sequence_a: assert property (disable iff(rst)STARTPARSING__blasting__READY_to_STARTPARSING_p_sequence(bitNum));
 STARTPARSING__blasting__READY_to_STARTPARSING_p_sequence_NOT_a: assert property (disable iff(rst)STARTPARSING__blasting__READY_to_STARTPARSING_p_sequence_NOT(bitNum));
end

property STARTPARSING__blasting__READY_to_STARTPARSING_p_sequence(bitPos);
 READY_to_STARTPARSING_p_sequence
|->
 ##1 RefinementVector[bitPos];
endproperty

property STARTPARSING__blasting__READY_to_STARTPARSING_p_sequence_NOT(bitPos);
 READY_to_STARTPARSING_p_sequence
|->
 ##1 !RefinementVector[bitPos];
endproperty

//STARTPARSING_to_STARTPARSING_p_sequence
for(genvar bitNum = 0; bitNum < 18 ; bitNum++) begin: STARTPARSING__blasting__STARTPARSING_to_STARTPARSING_p_sequence_gen
 STARTPARSING__blasting__STARTPARSING_to_STARTPARSING_p_sequence_a: assert property (disable iff(rst)STARTPARSING__blasting__STARTPARSING_to_STARTPARSING_p_sequence(bitNum));
 STARTPARSING__blasting__STARTPARSING_to_STARTPARSING_p_sequence_NOT_a: assert property (disable iff(rst)STARTPARSING__blasting__STARTPARSING_to_STARTPARSING_p_sequence_NOT(bitNum));
end

property STARTPARSING__blasting__STARTPARSING_to_STARTPARSING_p_sequence(bitPos);
 STARTPARSING_to_STARTPARSING_p_sequence
|->
 ##1 RefinementVector[bitPos];
endproperty

property STARTPARSING__blasting__STARTPARSING_to_STARTPARSING_p_sequence_NOT(bitPos);
 STARTPARSING_to_STARTPARSING_p_sequence
|->
 ##1 !RefinementVector[bitPos];
endproperty


//Bit pairing properties

/********************************************/
/* DATAPARSING state bit-pairing properties */
/********************************************/

//DATAPARSING_to_DATAPARSING_1_p_sequence
//pair: {0,2}
DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_1_p_sequence__0__0_2_a: assert property (disable iff(rst) DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_1_p_sequence__0__0_2);
property DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_1_p_sequence__0__0_2;
 DATAPARSING_to_DATAPARSING_1_p_sequence
|->
 ##1 !RefinementVector[0]
 && !RefinementVector[2];
endproperty

DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_1_p_sequence__1__0_2_a: assert property (disable iff(rst) DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_1_p_sequence__1__0_2);
property DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_1_p_sequence__1__0_2;
 DATAPARSING_to_DATAPARSING_1_p_sequence
|->
 ##1 RefinementVector[0]
 && !RefinementVector[2];
endproperty

DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_1_p_sequence__2__0_2_a: assert property (disable iff(rst) DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_1_p_sequence__2__0_2);
property DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_1_p_sequence__2__0_2;
 DATAPARSING_to_DATAPARSING_1_p_sequence
|->
 ##1 !RefinementVector[0]
 && RefinementVector[2];
endproperty

DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_1_p_sequence__3__0_2_a: assert property (disable iff(rst) DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_1_p_sequence__3__0_2);
property DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_1_p_sequence__3__0_2;
 DATAPARSING_to_DATAPARSING_1_p_sequence
|->
 ##1 RefinementVector[0]
 && RefinementVector[2];
endproperty

//DATAPARSING_to_DATAPARSING_1_p_sequence
//pair: {2,10}
DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_1_p_sequence__0__2_10_a: assert property (disable iff(rst) DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_1_p_sequence__0__2_10);
property DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_1_p_sequence__0__2_10;
 DATAPARSING_to_DATAPARSING_1_p_sequence
|->
 ##1 !RefinementVector[2]
 && !RefinementVector[10];
endproperty

DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_1_p_sequence__1__2_10_a: assert property (disable iff(rst) DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_1_p_sequence__1__2_10);
property DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_1_p_sequence__1__2_10;
 DATAPARSING_to_DATAPARSING_1_p_sequence
|->
 ##1 RefinementVector[2]
 && !RefinementVector[10];
endproperty

DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_1_p_sequence__2__2_10_a: assert property (disable iff(rst) DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_1_p_sequence__2__2_10);
property DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_1_p_sequence__2__2_10;
 DATAPARSING_to_DATAPARSING_1_p_sequence
|->
 ##1 !RefinementVector[2]
 && RefinementVector[10];
endproperty

DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_1_p_sequence__3__2_10_a: assert property (disable iff(rst) DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_1_p_sequence__3__2_10);
property DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_1_p_sequence__3__2_10;
 DATAPARSING_to_DATAPARSING_1_p_sequence
|->
 ##1 RefinementVector[2]
 && RefinementVector[10];
endproperty

//DATAPARSING_to_DATAPARSING_1_p_sequence
//pair: {10,14}
DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_1_p_sequence__0__10_14_a: assert property (disable iff(rst) DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_1_p_sequence__0__10_14);
property DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_1_p_sequence__0__10_14;
 DATAPARSING_to_DATAPARSING_1_p_sequence
|->
 ##1 !RefinementVector[10]
 && !RefinementVector[14];
endproperty

DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_1_p_sequence__1__10_14_a: assert property (disable iff(rst) DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_1_p_sequence__1__10_14);
property DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_1_p_sequence__1__10_14;
 DATAPARSING_to_DATAPARSING_1_p_sequence
|->
 ##1 RefinementVector[10]
 && !RefinementVector[14];
endproperty

DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_1_p_sequence__2__10_14_a: assert property (disable iff(rst) DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_1_p_sequence__2__10_14);
property DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_1_p_sequence__2__10_14;
 DATAPARSING_to_DATAPARSING_1_p_sequence
|->
 ##1 !RefinementVector[10]
 && RefinementVector[14];
endproperty

DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_1_p_sequence__3__10_14_a: assert property (disable iff(rst) DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_1_p_sequence__3__10_14);
property DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_1_p_sequence__3__10_14;
 DATAPARSING_to_DATAPARSING_1_p_sequence
|->
 ##1 RefinementVector[10]
 && RefinementVector[14];
endproperty


//DATAPARSING_to_DATAPARSING_2_p_sequence
//pair: {0,2}
DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_2_p_sequence__0__0_2_a: assert property (disable iff(rst) DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_2_p_sequence__0__0_2);
property DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_2_p_sequence__0__0_2;
 DATAPARSING_to_DATAPARSING_2_p_sequence
|->
 ##1 !RefinementVector[0]
 && !RefinementVector[2];
endproperty

DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_2_p_sequence__1__0_2_a: assert property (disable iff(rst) DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_2_p_sequence__1__0_2);
property DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_2_p_sequence__1__0_2;
 DATAPARSING_to_DATAPARSING_2_p_sequence
|->
 ##1 RefinementVector[0]
 && !RefinementVector[2];
endproperty

DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_2_p_sequence__2__0_2_a: assert property (disable iff(rst) DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_2_p_sequence__2__0_2);
property DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_2_p_sequence__2__0_2;
 DATAPARSING_to_DATAPARSING_2_p_sequence
|->
 ##1 !RefinementVector[0]
 && RefinementVector[2];
endproperty

DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_2_p_sequence__3__0_2_a: assert property (disable iff(rst) DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_2_p_sequence__3__0_2);
property DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_2_p_sequence__3__0_2;
 DATAPARSING_to_DATAPARSING_2_p_sequence
|->
 ##1 RefinementVector[0]
 && RefinementVector[2];
endproperty

//DATAPARSING_to_DATAPARSING_2_p_sequence
//pair: {2,10}
DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_2_p_sequence__0__2_10_a: assert property (disable iff(rst) DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_2_p_sequence__0__2_10);
property DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_2_p_sequence__0__2_10;
 DATAPARSING_to_DATAPARSING_2_p_sequence
|->
 ##1 !RefinementVector[2]
 && !RefinementVector[10];
endproperty

DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_2_p_sequence__1__2_10_a: assert property (disable iff(rst) DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_2_p_sequence__1__2_10);
property DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_2_p_sequence__1__2_10;
 DATAPARSING_to_DATAPARSING_2_p_sequence
|->
 ##1 RefinementVector[2]
 && !RefinementVector[10];
endproperty

DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_2_p_sequence__2__2_10_a: assert property (disable iff(rst) DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_2_p_sequence__2__2_10);
property DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_2_p_sequence__2__2_10;
 DATAPARSING_to_DATAPARSING_2_p_sequence
|->
 ##1 !RefinementVector[2]
 && RefinementVector[10];
endproperty

DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_2_p_sequence__3__2_10_a: assert property (disable iff(rst) DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_2_p_sequence__3__2_10);
property DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_2_p_sequence__3__2_10;
 DATAPARSING_to_DATAPARSING_2_p_sequence
|->
 ##1 RefinementVector[2]
 && RefinementVector[10];
endproperty


//DATAPARSING_to_DATAPARSING_p_sequence
//pair: {0,2}
DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_p_sequence__0__0_2_a: assert property (disable iff(rst) DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_p_sequence__0__0_2);
property DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_p_sequence__0__0_2;
 DATAPARSING_to_DATAPARSING_p_sequence
|->
 ##1 !RefinementVector[0]
 && !RefinementVector[2];
endproperty

DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_p_sequence__1__0_2_a: assert property (disable iff(rst) DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_p_sequence__1__0_2);
property DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_p_sequence__1__0_2;
 DATAPARSING_to_DATAPARSING_p_sequence
|->
 ##1 RefinementVector[0]
 && !RefinementVector[2];
endproperty

DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_p_sequence__2__0_2_a: assert property (disable iff(rst) DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_p_sequence__2__0_2);
property DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_p_sequence__2__0_2;
 DATAPARSING_to_DATAPARSING_p_sequence
|->
 ##1 !RefinementVector[0]
 && RefinementVector[2];
endproperty

DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_p_sequence__3__0_2_a: assert property (disable iff(rst) DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_p_sequence__3__0_2);
property DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_p_sequence__3__0_2;
 DATAPARSING_to_DATAPARSING_p_sequence
|->
 ##1 RefinementVector[0]
 && RefinementVector[2];
endproperty

//DATAPARSING_to_DATAPARSING_p_sequence
//pair: {2,10}
DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_p_sequence__0__2_10_a: assert property (disable iff(rst) DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_p_sequence__0__2_10);
property DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_p_sequence__0__2_10;
 DATAPARSING_to_DATAPARSING_p_sequence
|->
 ##1 !RefinementVector[2]
 && !RefinementVector[10];
endproperty

DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_p_sequence__1__2_10_a: assert property (disable iff(rst) DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_p_sequence__1__2_10);
property DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_p_sequence__1__2_10;
 DATAPARSING_to_DATAPARSING_p_sequence
|->
 ##1 RefinementVector[2]
 && !RefinementVector[10];
endproperty

DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_p_sequence__2__2_10_a: assert property (disable iff(rst) DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_p_sequence__2__2_10);
property DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_p_sequence__2__2_10;
 DATAPARSING_to_DATAPARSING_p_sequence
|->
 ##1 !RefinementVector[2]
 && RefinementVector[10];
endproperty

DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_p_sequence__3__2_10_a: assert property (disable iff(rst) DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_p_sequence__3__2_10);
property DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_p_sequence__3__2_10;
 DATAPARSING_to_DATAPARSING_p_sequence
|->
 ##1 RefinementVector[2]
 && RefinementVector[10];
endproperty

//DATAPARSING_to_DATAPARSING_p_sequence
//pair: {10,14}
DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_p_sequence__0__10_14_a: assert property (disable iff(rst) DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_p_sequence__0__10_14);
property DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_p_sequence__0__10_14;
 DATAPARSING_to_DATAPARSING_p_sequence
|->
 ##1 !RefinementVector[10]
 && !RefinementVector[14];
endproperty

DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_p_sequence__1__10_14_a: assert property (disable iff(rst) DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_p_sequence__1__10_14);
property DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_p_sequence__1__10_14;
 DATAPARSING_to_DATAPARSING_p_sequence
|->
 ##1 RefinementVector[10]
 && !RefinementVector[14];
endproperty

DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_p_sequence__2__10_14_a: assert property (disable iff(rst) DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_p_sequence__2__10_14);
property DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_p_sequence__2__10_14;
 DATAPARSING_to_DATAPARSING_p_sequence
|->
 ##1 !RefinementVector[10]
 && RefinementVector[14];
endproperty

DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_p_sequence__3__10_14_a: assert property (disable iff(rst) DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_p_sequence__3__10_14);
property DATAPARSING__pairing__DATAPARSING_to_DATAPARSING_p_sequence__3__10_14;
 DATAPARSING_to_DATAPARSING_p_sequence
|->
 ##1 RefinementVector[10]
 && RefinementVector[14];
endproperty


//INFOPARSING_to_DATAPARSING_1_p_sequence
//pair: {0,10}
DATAPARSING__pairing__INFOPARSING_to_DATAPARSING_1_p_sequence__0__0_10_a: assert property (disable iff(rst) DATAPARSING__pairing__INFOPARSING_to_DATAPARSING_1_p_sequence__0__0_10);
property DATAPARSING__pairing__INFOPARSING_to_DATAPARSING_1_p_sequence__0__0_10;
 INFOPARSING_to_DATAPARSING_1_p_sequence
|->
 ##1 !RefinementVector[0]
 && !RefinementVector[10];
endproperty

DATAPARSING__pairing__INFOPARSING_to_DATAPARSING_1_p_sequence__1__0_10_a: assert property (disable iff(rst) DATAPARSING__pairing__INFOPARSING_to_DATAPARSING_1_p_sequence__1__0_10);
property DATAPARSING__pairing__INFOPARSING_to_DATAPARSING_1_p_sequence__1__0_10;
 INFOPARSING_to_DATAPARSING_1_p_sequence
|->
 ##1 RefinementVector[0]
 && !RefinementVector[10];
endproperty

DATAPARSING__pairing__INFOPARSING_to_DATAPARSING_1_p_sequence__2__0_10_a: assert property (disable iff(rst) DATAPARSING__pairing__INFOPARSING_to_DATAPARSING_1_p_sequence__2__0_10);
property DATAPARSING__pairing__INFOPARSING_to_DATAPARSING_1_p_sequence__2__0_10;
 INFOPARSING_to_DATAPARSING_1_p_sequence
|->
 ##1 !RefinementVector[0]
 && RefinementVector[10];
endproperty

DATAPARSING__pairing__INFOPARSING_to_DATAPARSING_1_p_sequence__3__0_10_a: assert property (disable iff(rst) DATAPARSING__pairing__INFOPARSING_to_DATAPARSING_1_p_sequence__3__0_10);
property DATAPARSING__pairing__INFOPARSING_to_DATAPARSING_1_p_sequence__3__0_10;
 INFOPARSING_to_DATAPARSING_1_p_sequence
|->
 ##1 RefinementVector[0]
 && RefinementVector[10];
endproperty


//INFOPARSING_to_DATAPARSING_p_sequence
//pair: {0,10}
DATAPARSING__pairing__INFOPARSING_to_DATAPARSING_p_sequence__0__0_10_a: assert property (disable iff(rst) DATAPARSING__pairing__INFOPARSING_to_DATAPARSING_p_sequence__0__0_10);
property DATAPARSING__pairing__INFOPARSING_to_DATAPARSING_p_sequence__0__0_10;
 INFOPARSING_to_DATAPARSING_p_sequence
|->
 ##1 !RefinementVector[0]
 && !RefinementVector[10];
endproperty

DATAPARSING__pairing__INFOPARSING_to_DATAPARSING_p_sequence__1__0_10_a: assert property (disable iff(rst) DATAPARSING__pairing__INFOPARSING_to_DATAPARSING_p_sequence__1__0_10);
property DATAPARSING__pairing__INFOPARSING_to_DATAPARSING_p_sequence__1__0_10;
 INFOPARSING_to_DATAPARSING_p_sequence
|->
 ##1 RefinementVector[0]
 && !RefinementVector[10];
endproperty

DATAPARSING__pairing__INFOPARSING_to_DATAPARSING_p_sequence__2__0_10_a: assert property (disable iff(rst) DATAPARSING__pairing__INFOPARSING_to_DATAPARSING_p_sequence__2__0_10);
property DATAPARSING__pairing__INFOPARSING_to_DATAPARSING_p_sequence__2__0_10;
 INFOPARSING_to_DATAPARSING_p_sequence
|->
 ##1 !RefinementVector[0]
 && RefinementVector[10];
endproperty

DATAPARSING__pairing__INFOPARSING_to_DATAPARSING_p_sequence__3__0_10_a: assert property (disable iff(rst) DATAPARSING__pairing__INFOPARSING_to_DATAPARSING_p_sequence__3__0_10);
property DATAPARSING__pairing__INFOPARSING_to_DATAPARSING_p_sequence__3__0_10;
 INFOPARSING_to_DATAPARSING_p_sequence
|->
 ##1 RefinementVector[0]
 && RefinementVector[10];
endproperty


//STARTPARSING_to_DATAPARSING_1_p_sequence
//pair: {0,10}
DATAPARSING__pairing__STARTPARSING_to_DATAPARSING_1_p_sequence__0__0_10_a: assert property (disable iff(rst) DATAPARSING__pairing__STARTPARSING_to_DATAPARSING_1_p_sequence__0__0_10);
property DATAPARSING__pairing__STARTPARSING_to_DATAPARSING_1_p_sequence__0__0_10;
 STARTPARSING_to_DATAPARSING_1_p_sequence
|->
 ##1 !RefinementVector[0]
 && !RefinementVector[10];
endproperty

DATAPARSING__pairing__STARTPARSING_to_DATAPARSING_1_p_sequence__1__0_10_a: assert property (disable iff(rst) DATAPARSING__pairing__STARTPARSING_to_DATAPARSING_1_p_sequence__1__0_10);
property DATAPARSING__pairing__STARTPARSING_to_DATAPARSING_1_p_sequence__1__0_10;
 STARTPARSING_to_DATAPARSING_1_p_sequence
|->
 ##1 RefinementVector[0]
 && !RefinementVector[10];
endproperty

DATAPARSING__pairing__STARTPARSING_to_DATAPARSING_1_p_sequence__2__0_10_a: assert property (disable iff(rst) DATAPARSING__pairing__STARTPARSING_to_DATAPARSING_1_p_sequence__2__0_10);
property DATAPARSING__pairing__STARTPARSING_to_DATAPARSING_1_p_sequence__2__0_10;
 STARTPARSING_to_DATAPARSING_1_p_sequence
|->
 ##1 !RefinementVector[0]
 && RefinementVector[10];
endproperty

DATAPARSING__pairing__STARTPARSING_to_DATAPARSING_1_p_sequence__3__0_10_a: assert property (disable iff(rst) DATAPARSING__pairing__STARTPARSING_to_DATAPARSING_1_p_sequence__3__0_10);
property DATAPARSING__pairing__STARTPARSING_to_DATAPARSING_1_p_sequence__3__0_10;
 STARTPARSING_to_DATAPARSING_1_p_sequence
|->
 ##1 RefinementVector[0]
 && RefinementVector[10];
endproperty


//STARTPARSING_to_DATAPARSING_p_sequence
//pair: {0,10}
DATAPARSING__pairing__STARTPARSING_to_DATAPARSING_p_sequence__0__0_10_a: assert property (disable iff(rst) DATAPARSING__pairing__STARTPARSING_to_DATAPARSING_p_sequence__0__0_10);
property DATAPARSING__pairing__STARTPARSING_to_DATAPARSING_p_sequence__0__0_10;
 STARTPARSING_to_DATAPARSING_p_sequence
|->
 ##1 !RefinementVector[0]
 && !RefinementVector[10];
endproperty

DATAPARSING__pairing__STARTPARSING_to_DATAPARSING_p_sequence__1__0_10_a: assert property (disable iff(rst) DATAPARSING__pairing__STARTPARSING_to_DATAPARSING_p_sequence__1__0_10);
property DATAPARSING__pairing__STARTPARSING_to_DATAPARSING_p_sequence__1__0_10;
 STARTPARSING_to_DATAPARSING_p_sequence
|->
 ##1 RefinementVector[0]
 && !RefinementVector[10];
endproperty

DATAPARSING__pairing__STARTPARSING_to_DATAPARSING_p_sequence__2__0_10_a: assert property (disable iff(rst) DATAPARSING__pairing__STARTPARSING_to_DATAPARSING_p_sequence__2__0_10);
property DATAPARSING__pairing__STARTPARSING_to_DATAPARSING_p_sequence__2__0_10;
 STARTPARSING_to_DATAPARSING_p_sequence
|->
 ##1 !RefinementVector[0]
 && RefinementVector[10];
endproperty

DATAPARSING__pairing__STARTPARSING_to_DATAPARSING_p_sequence__3__0_10_a: assert property (disable iff(rst) DATAPARSING__pairing__STARTPARSING_to_DATAPARSING_p_sequence__3__0_10);
property DATAPARSING__pairing__STARTPARSING_to_DATAPARSING_p_sequence__3__0_10;
 STARTPARSING_to_DATAPARSING_p_sequence
|->
 ##1 RefinementVector[0]
 && RefinementVector[10];
endproperty


/*************************************/
/* DONE state bit-pairing properties */
/*************************************/

//DATAPARSING_to_DONE_p_sequence
//pair: {0,2}
DONE__pairing__DATAPARSING_to_DONE_p_sequence__0__0_2_a: assert property (disable iff(rst) DONE__pairing__DATAPARSING_to_DONE_p_sequence__0__0_2);
property DONE__pairing__DATAPARSING_to_DONE_p_sequence__0__0_2;
 DATAPARSING_to_DONE_p_sequence
|->
 ##1 !RefinementVector[0]
 && !RefinementVector[2];
endproperty

DONE__pairing__DATAPARSING_to_DONE_p_sequence__1__0_2_a: assert property (disable iff(rst) DONE__pairing__DATAPARSING_to_DONE_p_sequence__1__0_2);
property DONE__pairing__DATAPARSING_to_DONE_p_sequence__1__0_2;
 DATAPARSING_to_DONE_p_sequence
|->
 ##1 RefinementVector[0]
 && !RefinementVector[2];
endproperty

DONE__pairing__DATAPARSING_to_DONE_p_sequence__2__0_2_a: assert property (disable iff(rst) DONE__pairing__DATAPARSING_to_DONE_p_sequence__2__0_2);
property DONE__pairing__DATAPARSING_to_DONE_p_sequence__2__0_2;
 DATAPARSING_to_DONE_p_sequence
|->
 ##1 !RefinementVector[0]
 && RefinementVector[2];
endproperty

DONE__pairing__DATAPARSING_to_DONE_p_sequence__3__0_2_a: assert property (disable iff(rst) DONE__pairing__DATAPARSING_to_DONE_p_sequence__3__0_2);
property DONE__pairing__DATAPARSING_to_DONE_p_sequence__3__0_2;
 DATAPARSING_to_DONE_p_sequence
|->
 ##1 RefinementVector[0]
 && RefinementVector[2];
endproperty

//DATAPARSING_to_DONE_p_sequence
//pair: {2,3}
DONE__pairing__DATAPARSING_to_DONE_p_sequence__0__2_3_a: assert property (disable iff(rst) DONE__pairing__DATAPARSING_to_DONE_p_sequence__0__2_3);
property DONE__pairing__DATAPARSING_to_DONE_p_sequence__0__2_3;
 DATAPARSING_to_DONE_p_sequence
|->
 ##1 !RefinementVector[2]
 && !RefinementVector[3];
endproperty

DONE__pairing__DATAPARSING_to_DONE_p_sequence__1__2_3_a: assert property (disable iff(rst) DONE__pairing__DATAPARSING_to_DONE_p_sequence__1__2_3);
property DONE__pairing__DATAPARSING_to_DONE_p_sequence__1__2_3;
 DATAPARSING_to_DONE_p_sequence
|->
 ##1 RefinementVector[2]
 && !RefinementVector[3];
endproperty

DONE__pairing__DATAPARSING_to_DONE_p_sequence__2__2_3_a: assert property (disable iff(rst) DONE__pairing__DATAPARSING_to_DONE_p_sequence__2__2_3);
property DONE__pairing__DATAPARSING_to_DONE_p_sequence__2__2_3;
 DATAPARSING_to_DONE_p_sequence
|->
 ##1 !RefinementVector[2]
 && RefinementVector[3];
endproperty

DONE__pairing__DATAPARSING_to_DONE_p_sequence__3__2_3_a: assert property (disable iff(rst) DONE__pairing__DATAPARSING_to_DONE_p_sequence__3__2_3);
property DONE__pairing__DATAPARSING_to_DONE_p_sequence__3__2_3;
 DATAPARSING_to_DONE_p_sequence
|->
 ##1 RefinementVector[2]
 && RefinementVector[3];
endproperty

//DATAPARSING_to_DONE_p_sequence
//pair: {3,10}
DONE__pairing__DATAPARSING_to_DONE_p_sequence__0__3_10_a: assert property (disable iff(rst) DONE__pairing__DATAPARSING_to_DONE_p_sequence__0__3_10);
property DONE__pairing__DATAPARSING_to_DONE_p_sequence__0__3_10;
 DATAPARSING_to_DONE_p_sequence
|->
 ##1 !RefinementVector[3]
 && !RefinementVector[10];
endproperty

DONE__pairing__DATAPARSING_to_DONE_p_sequence__1__3_10_a: assert property (disable iff(rst) DONE__pairing__DATAPARSING_to_DONE_p_sequence__1__3_10);
property DONE__pairing__DATAPARSING_to_DONE_p_sequence__1__3_10;
 DATAPARSING_to_DONE_p_sequence
|->
 ##1 RefinementVector[3]
 && !RefinementVector[10];
endproperty

DONE__pairing__DATAPARSING_to_DONE_p_sequence__2__3_10_a: assert property (disable iff(rst) DONE__pairing__DATAPARSING_to_DONE_p_sequence__2__3_10);
property DONE__pairing__DATAPARSING_to_DONE_p_sequence__2__3_10;
 DATAPARSING_to_DONE_p_sequence
|->
 ##1 !RefinementVector[3]
 && RefinementVector[10];
endproperty

DONE__pairing__DATAPARSING_to_DONE_p_sequence__3__3_10_a: assert property (disable iff(rst) DONE__pairing__DATAPARSING_to_DONE_p_sequence__3__3_10);
property DONE__pairing__DATAPARSING_to_DONE_p_sequence__3__3_10;
 DATAPARSING_to_DONE_p_sequence
|->
 ##1 RefinementVector[3]
 && RefinementVector[10];
endproperty

//DATAPARSING_to_DONE_p_sequence
//pair: {10,12}
DONE__pairing__DATAPARSING_to_DONE_p_sequence__0__10_12_a: assert property (disable iff(rst) DONE__pairing__DATAPARSING_to_DONE_p_sequence__0__10_12);
property DONE__pairing__DATAPARSING_to_DONE_p_sequence__0__10_12;
 DATAPARSING_to_DONE_p_sequence
|->
 ##1 !RefinementVector[10]
 && !RefinementVector[12];
endproperty

DONE__pairing__DATAPARSING_to_DONE_p_sequence__1__10_12_a: assert property (disable iff(rst) DONE__pairing__DATAPARSING_to_DONE_p_sequence__1__10_12);
property DONE__pairing__DATAPARSING_to_DONE_p_sequence__1__10_12;
 DATAPARSING_to_DONE_p_sequence
|->
 ##1 RefinementVector[10]
 && !RefinementVector[12];
endproperty

DONE__pairing__DATAPARSING_to_DONE_p_sequence__2__10_12_a: assert property (disable iff(rst) DONE__pairing__DATAPARSING_to_DONE_p_sequence__2__10_12);
property DONE__pairing__DATAPARSING_to_DONE_p_sequence__2__10_12;
 DATAPARSING_to_DONE_p_sequence
|->
 ##1 !RefinementVector[10]
 && RefinementVector[12];
endproperty

DONE__pairing__DATAPARSING_to_DONE_p_sequence__3__10_12_a: assert property (disable iff(rst) DONE__pairing__DATAPARSING_to_DONE_p_sequence__3__10_12);
property DONE__pairing__DATAPARSING_to_DONE_p_sequence__3__10_12;
 DATAPARSING_to_DONE_p_sequence
|->
 ##1 RefinementVector[10]
 && RefinementVector[12];
endproperty

//DATAPARSING_to_DONE_p_sequence
//pair: {12,14}
DONE__pairing__DATAPARSING_to_DONE_p_sequence__0__12_14_a: assert property (disable iff(rst) DONE__pairing__DATAPARSING_to_DONE_p_sequence__0__12_14);
property DONE__pairing__DATAPARSING_to_DONE_p_sequence__0__12_14;
 DATAPARSING_to_DONE_p_sequence
|->
 ##1 !RefinementVector[12]
 && !RefinementVector[14];
endproperty

DONE__pairing__DATAPARSING_to_DONE_p_sequence__1__12_14_a: assert property (disable iff(rst) DONE__pairing__DATAPARSING_to_DONE_p_sequence__1__12_14);
property DONE__pairing__DATAPARSING_to_DONE_p_sequence__1__12_14;
 DATAPARSING_to_DONE_p_sequence
|->
 ##1 RefinementVector[12]
 && !RefinementVector[14];
endproperty

DONE__pairing__DATAPARSING_to_DONE_p_sequence__2__12_14_a: assert property (disable iff(rst) DONE__pairing__DATAPARSING_to_DONE_p_sequence__2__12_14);
property DONE__pairing__DATAPARSING_to_DONE_p_sequence__2__12_14;
 DATAPARSING_to_DONE_p_sequence
|->
 ##1 !RefinementVector[12]
 && RefinementVector[14];
endproperty

DONE__pairing__DATAPARSING_to_DONE_p_sequence__3__12_14_a: assert property (disable iff(rst) DONE__pairing__DATAPARSING_to_DONE_p_sequence__3__12_14);
property DONE__pairing__DATAPARSING_to_DONE_p_sequence__3__12_14;
 DATAPARSING_to_DONE_p_sequence
|->
 ##1 RefinementVector[12]
 && RefinementVector[14];
endproperty


//DONE_wait_p_sequence
//pair: {0,1}
DONE__pairing__DONE_wait_p_sequence__0__0_1_a: assert property (disable iff(rst) DONE__pairing__DONE_wait_p_sequence__0__0_1);
property DONE__pairing__DONE_wait_p_sequence__0__0_1;
 DONE_wait_p_sequence
|->
 ##1 !RefinementVector[0]
 && !RefinementVector[1];
endproperty

DONE__pairing__DONE_wait_p_sequence__1__0_1_a: assert property (disable iff(rst) DONE__pairing__DONE_wait_p_sequence__1__0_1);
property DONE__pairing__DONE_wait_p_sequence__1__0_1;
 DONE_wait_p_sequence
|->
 ##1 RefinementVector[0]
 && !RefinementVector[1];
endproperty

DONE__pairing__DONE_wait_p_sequence__2__0_1_a: assert property (disable iff(rst) DONE__pairing__DONE_wait_p_sequence__2__0_1);
property DONE__pairing__DONE_wait_p_sequence__2__0_1;
 DONE_wait_p_sequence
|->
 ##1 !RefinementVector[0]
 && RefinementVector[1];
endproperty

DONE__pairing__DONE_wait_p_sequence__3__0_1_a: assert property (disable iff(rst) DONE__pairing__DONE_wait_p_sequence__3__0_1);
property DONE__pairing__DONE_wait_p_sequence__3__0_1;
 DONE_wait_p_sequence
|->
 ##1 RefinementVector[0]
 && RefinementVector[1];
endproperty

//DONE_wait_p_sequence
//pair: {1,2}
DONE__pairing__DONE_wait_p_sequence__0__1_2_a: assert property (disable iff(rst) DONE__pairing__DONE_wait_p_sequence__0__1_2);
property DONE__pairing__DONE_wait_p_sequence__0__1_2;
 DONE_wait_p_sequence
|->
 ##1 !RefinementVector[1]
 && !RefinementVector[2];
endproperty

DONE__pairing__DONE_wait_p_sequence__1__1_2_a: assert property (disable iff(rst) DONE__pairing__DONE_wait_p_sequence__1__1_2);
property DONE__pairing__DONE_wait_p_sequence__1__1_2;
 DONE_wait_p_sequence
|->
 ##1 RefinementVector[1]
 && !RefinementVector[2];
endproperty

DONE__pairing__DONE_wait_p_sequence__2__1_2_a: assert property (disable iff(rst) DONE__pairing__DONE_wait_p_sequence__2__1_2);
property DONE__pairing__DONE_wait_p_sequence__2__1_2;
 DONE_wait_p_sequence
|->
 ##1 !RefinementVector[1]
 && RefinementVector[2];
endproperty

DONE__pairing__DONE_wait_p_sequence__3__1_2_a: assert property (disable iff(rst) DONE__pairing__DONE_wait_p_sequence__3__1_2);
property DONE__pairing__DONE_wait_p_sequence__3__1_2;
 DONE_wait_p_sequence
|->
 ##1 RefinementVector[1]
 && RefinementVector[2];
endproperty

//DONE_wait_p_sequence
//pair: {2,3}
DONE__pairing__DONE_wait_p_sequence__0__2_3_a: assert property (disable iff(rst) DONE__pairing__DONE_wait_p_sequence__0__2_3);
property DONE__pairing__DONE_wait_p_sequence__0__2_3;
 DONE_wait_p_sequence
|->
 ##1 !RefinementVector[2]
 && !RefinementVector[3];
endproperty

DONE__pairing__DONE_wait_p_sequence__1__2_3_a: assert property (disable iff(rst) DONE__pairing__DONE_wait_p_sequence__1__2_3);
property DONE__pairing__DONE_wait_p_sequence__1__2_3;
 DONE_wait_p_sequence
|->
 ##1 RefinementVector[2]
 && !RefinementVector[3];
endproperty

DONE__pairing__DONE_wait_p_sequence__2__2_3_a: assert property (disable iff(rst) DONE__pairing__DONE_wait_p_sequence__2__2_3);
property DONE__pairing__DONE_wait_p_sequence__2__2_3;
 DONE_wait_p_sequence
|->
 ##1 !RefinementVector[2]
 && RefinementVector[3];
endproperty

DONE__pairing__DONE_wait_p_sequence__3__2_3_a: assert property (disable iff(rst) DONE__pairing__DONE_wait_p_sequence__3__2_3);
property DONE__pairing__DONE_wait_p_sequence__3__2_3;
 DONE_wait_p_sequence
|->
 ##1 RefinementVector[2]
 && RefinementVector[3];
endproperty

//DONE_wait_p_sequence
//pair: {3,4}
DONE__pairing__DONE_wait_p_sequence__0__3_4_a: assert property (disable iff(rst) DONE__pairing__DONE_wait_p_sequence__0__3_4);
property DONE__pairing__DONE_wait_p_sequence__0__3_4;
 DONE_wait_p_sequence
|->
 ##1 !RefinementVector[3]
 && !RefinementVector[4];
endproperty

DONE__pairing__DONE_wait_p_sequence__1__3_4_a: assert property (disable iff(rst) DONE__pairing__DONE_wait_p_sequence__1__3_4);
property DONE__pairing__DONE_wait_p_sequence__1__3_4;
 DONE_wait_p_sequence
|->
 ##1 RefinementVector[3]
 && !RefinementVector[4];
endproperty

DONE__pairing__DONE_wait_p_sequence__2__3_4_a: assert property (disable iff(rst) DONE__pairing__DONE_wait_p_sequence__2__3_4);
property DONE__pairing__DONE_wait_p_sequence__2__3_4;
 DONE_wait_p_sequence
|->
 ##1 !RefinementVector[3]
 && RefinementVector[4];
endproperty

DONE__pairing__DONE_wait_p_sequence__3__3_4_a: assert property (disable iff(rst) DONE__pairing__DONE_wait_p_sequence__3__3_4);
property DONE__pairing__DONE_wait_p_sequence__3__3_4;
 DONE_wait_p_sequence
|->
 ##1 RefinementVector[3]
 && RefinementVector[4];
endproperty

//DONE_wait_p_sequence
//pair: {4,5}
DONE__pairing__DONE_wait_p_sequence__0__4_5_a: assert property (disable iff(rst) DONE__pairing__DONE_wait_p_sequence__0__4_5);
property DONE__pairing__DONE_wait_p_sequence__0__4_5;
 DONE_wait_p_sequence
|->
 ##1 !RefinementVector[4]
 && !RefinementVector[5];
endproperty

DONE__pairing__DONE_wait_p_sequence__1__4_5_a: assert property (disable iff(rst) DONE__pairing__DONE_wait_p_sequence__1__4_5);
property DONE__pairing__DONE_wait_p_sequence__1__4_5;
 DONE_wait_p_sequence
|->
 ##1 RefinementVector[4]
 && !RefinementVector[5];
endproperty

DONE__pairing__DONE_wait_p_sequence__2__4_5_a: assert property (disable iff(rst) DONE__pairing__DONE_wait_p_sequence__2__4_5);
property DONE__pairing__DONE_wait_p_sequence__2__4_5;
 DONE_wait_p_sequence
|->
 ##1 !RefinementVector[4]
 && RefinementVector[5];
endproperty

DONE__pairing__DONE_wait_p_sequence__3__4_5_a: assert property (disable iff(rst) DONE__pairing__DONE_wait_p_sequence__3__4_5);
property DONE__pairing__DONE_wait_p_sequence__3__4_5;
 DONE_wait_p_sequence
|->
 ##1 RefinementVector[4]
 && RefinementVector[5];
endproperty

//DONE_wait_p_sequence
//pair: {5,6}
DONE__pairing__DONE_wait_p_sequence__0__5_6_a: assert property (disable iff(rst) DONE__pairing__DONE_wait_p_sequence__0__5_6);
property DONE__pairing__DONE_wait_p_sequence__0__5_6;
 DONE_wait_p_sequence
|->
 ##1 !RefinementVector[5]
 && !RefinementVector[6];
endproperty

DONE__pairing__DONE_wait_p_sequence__1__5_6_a: assert property (disable iff(rst) DONE__pairing__DONE_wait_p_sequence__1__5_6);
property DONE__pairing__DONE_wait_p_sequence__1__5_6;
 DONE_wait_p_sequence
|->
 ##1 RefinementVector[5]
 && !RefinementVector[6];
endproperty

DONE__pairing__DONE_wait_p_sequence__2__5_6_a: assert property (disable iff(rst) DONE__pairing__DONE_wait_p_sequence__2__5_6);
property DONE__pairing__DONE_wait_p_sequence__2__5_6;
 DONE_wait_p_sequence
|->
 ##1 !RefinementVector[5]
 && RefinementVector[6];
endproperty

DONE__pairing__DONE_wait_p_sequence__3__5_6_a: assert property (disable iff(rst) DONE__pairing__DONE_wait_p_sequence__3__5_6);
property DONE__pairing__DONE_wait_p_sequence__3__5_6;
 DONE_wait_p_sequence
|->
 ##1 RefinementVector[5]
 && RefinementVector[6];
endproperty

//DONE_wait_p_sequence
//pair: {6,10}
DONE__pairing__DONE_wait_p_sequence__0__6_10_a: assert property (disable iff(rst) DONE__pairing__DONE_wait_p_sequence__0__6_10);
property DONE__pairing__DONE_wait_p_sequence__0__6_10;
 DONE_wait_p_sequence
|->
 ##1 !RefinementVector[6]
 && !RefinementVector[10];
endproperty

DONE__pairing__DONE_wait_p_sequence__1__6_10_a: assert property (disable iff(rst) DONE__pairing__DONE_wait_p_sequence__1__6_10);
property DONE__pairing__DONE_wait_p_sequence__1__6_10;
 DONE_wait_p_sequence
|->
 ##1 RefinementVector[6]
 && !RefinementVector[10];
endproperty

DONE__pairing__DONE_wait_p_sequence__2__6_10_a: assert property (disable iff(rst) DONE__pairing__DONE_wait_p_sequence__2__6_10);
property DONE__pairing__DONE_wait_p_sequence__2__6_10;
 DONE_wait_p_sequence
|->
 ##1 !RefinementVector[6]
 && RefinementVector[10];
endproperty

DONE__pairing__DONE_wait_p_sequence__3__6_10_a: assert property (disable iff(rst) DONE__pairing__DONE_wait_p_sequence__3__6_10);
property DONE__pairing__DONE_wait_p_sequence__3__6_10;
 DONE_wait_p_sequence
|->
 ##1 RefinementVector[6]
 && RefinementVector[10];
endproperty

//DONE_wait_p_sequence
//pair: {10,12}
DONE__pairing__DONE_wait_p_sequence__0__10_12_a: assert property (disable iff(rst) DONE__pairing__DONE_wait_p_sequence__0__10_12);
property DONE__pairing__DONE_wait_p_sequence__0__10_12;
 DONE_wait_p_sequence
|->
 ##1 !RefinementVector[10]
 && !RefinementVector[12];
endproperty

DONE__pairing__DONE_wait_p_sequence__1__10_12_a: assert property (disable iff(rst) DONE__pairing__DONE_wait_p_sequence__1__10_12);
property DONE__pairing__DONE_wait_p_sequence__1__10_12;
 DONE_wait_p_sequence
|->
 ##1 RefinementVector[10]
 && !RefinementVector[12];
endproperty

DONE__pairing__DONE_wait_p_sequence__2__10_12_a: assert property (disable iff(rst) DONE__pairing__DONE_wait_p_sequence__2__10_12);
property DONE__pairing__DONE_wait_p_sequence__2__10_12;
 DONE_wait_p_sequence
|->
 ##1 !RefinementVector[10]
 && RefinementVector[12];
endproperty

DONE__pairing__DONE_wait_p_sequence__3__10_12_a: assert property (disable iff(rst) DONE__pairing__DONE_wait_p_sequence__3__10_12);
property DONE__pairing__DONE_wait_p_sequence__3__10_12;
 DONE_wait_p_sequence
|->
 ##1 RefinementVector[10]
 && RefinementVector[12];
endproperty

//DONE_wait_p_sequence
//pair: {12,14}
DONE__pairing__DONE_wait_p_sequence__0__12_14_a: assert property (disable iff(rst) DONE__pairing__DONE_wait_p_sequence__0__12_14);
property DONE__pairing__DONE_wait_p_sequence__0__12_14;
 DONE_wait_p_sequence
|->
 ##1 !RefinementVector[12]
 && !RefinementVector[14];
endproperty

DONE__pairing__DONE_wait_p_sequence__1__12_14_a: assert property (disable iff(rst) DONE__pairing__DONE_wait_p_sequence__1__12_14);
property DONE__pairing__DONE_wait_p_sequence__1__12_14;
 DONE_wait_p_sequence
|->
 ##1 RefinementVector[12]
 && !RefinementVector[14];
endproperty

DONE__pairing__DONE_wait_p_sequence__2__12_14_a: assert property (disable iff(rst) DONE__pairing__DONE_wait_p_sequence__2__12_14);
property DONE__pairing__DONE_wait_p_sequence__2__12_14;
 DONE_wait_p_sequence
|->
 ##1 !RefinementVector[12]
 && RefinementVector[14];
endproperty

DONE__pairing__DONE_wait_p_sequence__3__12_14_a: assert property (disable iff(rst) DONE__pairing__DONE_wait_p_sequence__3__12_14);
property DONE__pairing__DONE_wait_p_sequence__3__12_14;
 DONE_wait_p_sequence
|->
 ##1 RefinementVector[12]
 && RefinementVector[14];
endproperty


//ENDPARSING_to_DONE_p_sequence
//pair: {0,2}
DONE__pairing__ENDPARSING_to_DONE_p_sequence__0__0_2_a: assert property (disable iff(rst) DONE__pairing__ENDPARSING_to_DONE_p_sequence__0__0_2);
property DONE__pairing__ENDPARSING_to_DONE_p_sequence__0__0_2;
 ENDPARSING_to_DONE_p_sequence
|->
 ##1 !RefinementVector[0]
 && !RefinementVector[2];
endproperty

DONE__pairing__ENDPARSING_to_DONE_p_sequence__1__0_2_a: assert property (disable iff(rst) DONE__pairing__ENDPARSING_to_DONE_p_sequence__1__0_2);
property DONE__pairing__ENDPARSING_to_DONE_p_sequence__1__0_2;
 ENDPARSING_to_DONE_p_sequence
|->
 ##1 RefinementVector[0]
 && !RefinementVector[2];
endproperty

DONE__pairing__ENDPARSING_to_DONE_p_sequence__2__0_2_a: assert property (disable iff(rst) DONE__pairing__ENDPARSING_to_DONE_p_sequence__2__0_2);
property DONE__pairing__ENDPARSING_to_DONE_p_sequence__2__0_2;
 ENDPARSING_to_DONE_p_sequence
|->
 ##1 !RefinementVector[0]
 && RefinementVector[2];
endproperty

DONE__pairing__ENDPARSING_to_DONE_p_sequence__3__0_2_a: assert property (disable iff(rst) DONE__pairing__ENDPARSING_to_DONE_p_sequence__3__0_2);
property DONE__pairing__ENDPARSING_to_DONE_p_sequence__3__0_2;
 ENDPARSING_to_DONE_p_sequence
|->
 ##1 RefinementVector[0]
 && RefinementVector[2];
endproperty

//ENDPARSING_to_DONE_p_sequence
//pair: {2,3}
DONE__pairing__ENDPARSING_to_DONE_p_sequence__0__2_3_a: assert property (disable iff(rst) DONE__pairing__ENDPARSING_to_DONE_p_sequence__0__2_3);
property DONE__pairing__ENDPARSING_to_DONE_p_sequence__0__2_3;
 ENDPARSING_to_DONE_p_sequence
|->
 ##1 !RefinementVector[2]
 && !RefinementVector[3];
endproperty

DONE__pairing__ENDPARSING_to_DONE_p_sequence__1__2_3_a: assert property (disable iff(rst) DONE__pairing__ENDPARSING_to_DONE_p_sequence__1__2_3);
property DONE__pairing__ENDPARSING_to_DONE_p_sequence__1__2_3;
 ENDPARSING_to_DONE_p_sequence
|->
 ##1 RefinementVector[2]
 && !RefinementVector[3];
endproperty

DONE__pairing__ENDPARSING_to_DONE_p_sequence__2__2_3_a: assert property (disable iff(rst) DONE__pairing__ENDPARSING_to_DONE_p_sequence__2__2_3);
property DONE__pairing__ENDPARSING_to_DONE_p_sequence__2__2_3;
 ENDPARSING_to_DONE_p_sequence
|->
 ##1 !RefinementVector[2]
 && RefinementVector[3];
endproperty

DONE__pairing__ENDPARSING_to_DONE_p_sequence__3__2_3_a: assert property (disable iff(rst) DONE__pairing__ENDPARSING_to_DONE_p_sequence__3__2_3);
property DONE__pairing__ENDPARSING_to_DONE_p_sequence__3__2_3;
 ENDPARSING_to_DONE_p_sequence
|->
 ##1 RefinementVector[2]
 && RefinementVector[3];
endproperty

//ENDPARSING_to_DONE_p_sequence
//pair: {3,5}
DONE__pairing__ENDPARSING_to_DONE_p_sequence__0__3_5_a: assert property (disable iff(rst) DONE__pairing__ENDPARSING_to_DONE_p_sequence__0__3_5);
property DONE__pairing__ENDPARSING_to_DONE_p_sequence__0__3_5;
 ENDPARSING_to_DONE_p_sequence
|->
 ##1 !RefinementVector[3]
 && !RefinementVector[5];
endproperty

DONE__pairing__ENDPARSING_to_DONE_p_sequence__1__3_5_a: assert property (disable iff(rst) DONE__pairing__ENDPARSING_to_DONE_p_sequence__1__3_5);
property DONE__pairing__ENDPARSING_to_DONE_p_sequence__1__3_5;
 ENDPARSING_to_DONE_p_sequence
|->
 ##1 RefinementVector[3]
 && !RefinementVector[5];
endproperty

DONE__pairing__ENDPARSING_to_DONE_p_sequence__2__3_5_a: assert property (disable iff(rst) DONE__pairing__ENDPARSING_to_DONE_p_sequence__2__3_5);
property DONE__pairing__ENDPARSING_to_DONE_p_sequence__2__3_5;
 ENDPARSING_to_DONE_p_sequence
|->
 ##1 !RefinementVector[3]
 && RefinementVector[5];
endproperty

DONE__pairing__ENDPARSING_to_DONE_p_sequence__3__3_5_a: assert property (disable iff(rst) DONE__pairing__ENDPARSING_to_DONE_p_sequence__3__3_5);
property DONE__pairing__ENDPARSING_to_DONE_p_sequence__3__3_5;
 ENDPARSING_to_DONE_p_sequence
|->
 ##1 RefinementVector[3]
 && RefinementVector[5];
endproperty

//ENDPARSING_to_DONE_p_sequence
//pair: {5,10}
DONE__pairing__ENDPARSING_to_DONE_p_sequence__0__5_10_a: assert property (disable iff(rst) DONE__pairing__ENDPARSING_to_DONE_p_sequence__0__5_10);
property DONE__pairing__ENDPARSING_to_DONE_p_sequence__0__5_10;
 ENDPARSING_to_DONE_p_sequence
|->
 ##1 !RefinementVector[5]
 && !RefinementVector[10];
endproperty

DONE__pairing__ENDPARSING_to_DONE_p_sequence__1__5_10_a: assert property (disable iff(rst) DONE__pairing__ENDPARSING_to_DONE_p_sequence__1__5_10);
property DONE__pairing__ENDPARSING_to_DONE_p_sequence__1__5_10;
 ENDPARSING_to_DONE_p_sequence
|->
 ##1 RefinementVector[5]
 && !RefinementVector[10];
endproperty

DONE__pairing__ENDPARSING_to_DONE_p_sequence__2__5_10_a: assert property (disable iff(rst) DONE__pairing__ENDPARSING_to_DONE_p_sequence__2__5_10);
property DONE__pairing__ENDPARSING_to_DONE_p_sequence__2__5_10;
 ENDPARSING_to_DONE_p_sequence
|->
 ##1 !RefinementVector[5]
 && RefinementVector[10];
endproperty

DONE__pairing__ENDPARSING_to_DONE_p_sequence__3__5_10_a: assert property (disable iff(rst) DONE__pairing__ENDPARSING_to_DONE_p_sequence__3__5_10);
property DONE__pairing__ENDPARSING_to_DONE_p_sequence__3__5_10;
 ENDPARSING_to_DONE_p_sequence
|->
 ##1 RefinementVector[5]
 && RefinementVector[10];
endproperty

//ENDPARSING_to_DONE_p_sequence
//pair: {10,12}
DONE__pairing__ENDPARSING_to_DONE_p_sequence__0__10_12_a: assert property (disable iff(rst) DONE__pairing__ENDPARSING_to_DONE_p_sequence__0__10_12);
property DONE__pairing__ENDPARSING_to_DONE_p_sequence__0__10_12;
 ENDPARSING_to_DONE_p_sequence
|->
 ##1 !RefinementVector[10]
 && !RefinementVector[12];
endproperty

DONE__pairing__ENDPARSING_to_DONE_p_sequence__1__10_12_a: assert property (disable iff(rst) DONE__pairing__ENDPARSING_to_DONE_p_sequence__1__10_12);
property DONE__pairing__ENDPARSING_to_DONE_p_sequence__1__10_12;
 ENDPARSING_to_DONE_p_sequence
|->
 ##1 RefinementVector[10]
 && !RefinementVector[12];
endproperty

DONE__pairing__ENDPARSING_to_DONE_p_sequence__2__10_12_a: assert property (disable iff(rst) DONE__pairing__ENDPARSING_to_DONE_p_sequence__2__10_12);
property DONE__pairing__ENDPARSING_to_DONE_p_sequence__2__10_12;
 ENDPARSING_to_DONE_p_sequence
|->
 ##1 !RefinementVector[10]
 && RefinementVector[12];
endproperty

DONE__pairing__ENDPARSING_to_DONE_p_sequence__3__10_12_a: assert property (disable iff(rst) DONE__pairing__ENDPARSING_to_DONE_p_sequence__3__10_12);
property DONE__pairing__ENDPARSING_to_DONE_p_sequence__3__10_12;
 ENDPARSING_to_DONE_p_sequence
|->
 ##1 RefinementVector[10]
 && RefinementVector[12];
endproperty

//ENDPARSING_to_DONE_p_sequence
//pair: {12,14}
DONE__pairing__ENDPARSING_to_DONE_p_sequence__0__12_14_a: assert property (disable iff(rst) DONE__pairing__ENDPARSING_to_DONE_p_sequence__0__12_14);
property DONE__pairing__ENDPARSING_to_DONE_p_sequence__0__12_14;
 ENDPARSING_to_DONE_p_sequence
|->
 ##1 !RefinementVector[12]
 && !RefinementVector[14];
endproperty

DONE__pairing__ENDPARSING_to_DONE_p_sequence__1__12_14_a: assert property (disable iff(rst) DONE__pairing__ENDPARSING_to_DONE_p_sequence__1__12_14);
property DONE__pairing__ENDPARSING_to_DONE_p_sequence__1__12_14;
 ENDPARSING_to_DONE_p_sequence
|->
 ##1 RefinementVector[12]
 && !RefinementVector[14];
endproperty

DONE__pairing__ENDPARSING_to_DONE_p_sequence__2__12_14_a: assert property (disable iff(rst) DONE__pairing__ENDPARSING_to_DONE_p_sequence__2__12_14);
property DONE__pairing__ENDPARSING_to_DONE_p_sequence__2__12_14;
 ENDPARSING_to_DONE_p_sequence
|->
 ##1 !RefinementVector[12]
 && RefinementVector[14];
endproperty

DONE__pairing__ENDPARSING_to_DONE_p_sequence__3__12_14_a: assert property (disable iff(rst) DONE__pairing__ENDPARSING_to_DONE_p_sequence__3__12_14);
property DONE__pairing__ENDPARSING_to_DONE_p_sequence__3__12_14;
 ENDPARSING_to_DONE_p_sequence
|->
 ##1 RefinementVector[12]
 && RefinementVector[14];
endproperty


//INFOPARSING_to_DONE_p_sequence
//pair: {0,2}
DONE__pairing__INFOPARSING_to_DONE_p_sequence__0__0_2_a: assert property (disable iff(rst) DONE__pairing__INFOPARSING_to_DONE_p_sequence__0__0_2);
property DONE__pairing__INFOPARSING_to_DONE_p_sequence__0__0_2;
 INFOPARSING_to_DONE_p_sequence
|->
 ##1 !RefinementVector[0]
 && !RefinementVector[2];
endproperty

DONE__pairing__INFOPARSING_to_DONE_p_sequence__1__0_2_a: assert property (disable iff(rst) DONE__pairing__INFOPARSING_to_DONE_p_sequence__1__0_2);
property DONE__pairing__INFOPARSING_to_DONE_p_sequence__1__0_2;
 INFOPARSING_to_DONE_p_sequence
|->
 ##1 RefinementVector[0]
 && !RefinementVector[2];
endproperty

DONE__pairing__INFOPARSING_to_DONE_p_sequence__2__0_2_a: assert property (disable iff(rst) DONE__pairing__INFOPARSING_to_DONE_p_sequence__2__0_2);
property DONE__pairing__INFOPARSING_to_DONE_p_sequence__2__0_2;
 INFOPARSING_to_DONE_p_sequence
|->
 ##1 !RefinementVector[0]
 && RefinementVector[2];
endproperty

DONE__pairing__INFOPARSING_to_DONE_p_sequence__3__0_2_a: assert property (disable iff(rst) DONE__pairing__INFOPARSING_to_DONE_p_sequence__3__0_2);
property DONE__pairing__INFOPARSING_to_DONE_p_sequence__3__0_2;
 INFOPARSING_to_DONE_p_sequence
|->
 ##1 RefinementVector[0]
 && RefinementVector[2];
endproperty

//INFOPARSING_to_DONE_p_sequence
//pair: {2,3}
DONE__pairing__INFOPARSING_to_DONE_p_sequence__0__2_3_a: assert property (disable iff(rst) DONE__pairing__INFOPARSING_to_DONE_p_sequence__0__2_3);
property DONE__pairing__INFOPARSING_to_DONE_p_sequence__0__2_3;
 INFOPARSING_to_DONE_p_sequence
|->
 ##1 !RefinementVector[2]
 && !RefinementVector[3];
endproperty

DONE__pairing__INFOPARSING_to_DONE_p_sequence__1__2_3_a: assert property (disable iff(rst) DONE__pairing__INFOPARSING_to_DONE_p_sequence__1__2_3);
property DONE__pairing__INFOPARSING_to_DONE_p_sequence__1__2_3;
 INFOPARSING_to_DONE_p_sequence
|->
 ##1 RefinementVector[2]
 && !RefinementVector[3];
endproperty

DONE__pairing__INFOPARSING_to_DONE_p_sequence__2__2_3_a: assert property (disable iff(rst) DONE__pairing__INFOPARSING_to_DONE_p_sequence__2__2_3);
property DONE__pairing__INFOPARSING_to_DONE_p_sequence__2__2_3;
 INFOPARSING_to_DONE_p_sequence
|->
 ##1 !RefinementVector[2]
 && RefinementVector[3];
endproperty

DONE__pairing__INFOPARSING_to_DONE_p_sequence__3__2_3_a: assert property (disable iff(rst) DONE__pairing__INFOPARSING_to_DONE_p_sequence__3__2_3);
property DONE__pairing__INFOPARSING_to_DONE_p_sequence__3__2_3;
 INFOPARSING_to_DONE_p_sequence
|->
 ##1 RefinementVector[2]
 && RefinementVector[3];
endproperty

//INFOPARSING_to_DONE_p_sequence
//pair: {3,10}
DONE__pairing__INFOPARSING_to_DONE_p_sequence__0__3_10_a: assert property (disable iff(rst) DONE__pairing__INFOPARSING_to_DONE_p_sequence__0__3_10);
property DONE__pairing__INFOPARSING_to_DONE_p_sequence__0__3_10;
 INFOPARSING_to_DONE_p_sequence
|->
 ##1 !RefinementVector[3]
 && !RefinementVector[10];
endproperty

DONE__pairing__INFOPARSING_to_DONE_p_sequence__1__3_10_a: assert property (disable iff(rst) DONE__pairing__INFOPARSING_to_DONE_p_sequence__1__3_10);
property DONE__pairing__INFOPARSING_to_DONE_p_sequence__1__3_10;
 INFOPARSING_to_DONE_p_sequence
|->
 ##1 RefinementVector[3]
 && !RefinementVector[10];
endproperty

DONE__pairing__INFOPARSING_to_DONE_p_sequence__2__3_10_a: assert property (disable iff(rst) DONE__pairing__INFOPARSING_to_DONE_p_sequence__2__3_10);
property DONE__pairing__INFOPARSING_to_DONE_p_sequence__2__3_10;
 INFOPARSING_to_DONE_p_sequence
|->
 ##1 !RefinementVector[3]
 && RefinementVector[10];
endproperty

DONE__pairing__INFOPARSING_to_DONE_p_sequence__3__3_10_a: assert property (disable iff(rst) DONE__pairing__INFOPARSING_to_DONE_p_sequence__3__3_10);
property DONE__pairing__INFOPARSING_to_DONE_p_sequence__3__3_10;
 INFOPARSING_to_DONE_p_sequence
|->
 ##1 RefinementVector[3]
 && RefinementVector[10];
endproperty

//INFOPARSING_to_DONE_p_sequence
//pair: {10,12}
DONE__pairing__INFOPARSING_to_DONE_p_sequence__0__10_12_a: assert property (disable iff(rst) DONE__pairing__INFOPARSING_to_DONE_p_sequence__0__10_12);
property DONE__pairing__INFOPARSING_to_DONE_p_sequence__0__10_12;
 INFOPARSING_to_DONE_p_sequence
|->
 ##1 !RefinementVector[10]
 && !RefinementVector[12];
endproperty

DONE__pairing__INFOPARSING_to_DONE_p_sequence__1__10_12_a: assert property (disable iff(rst) DONE__pairing__INFOPARSING_to_DONE_p_sequence__1__10_12);
property DONE__pairing__INFOPARSING_to_DONE_p_sequence__1__10_12;
 INFOPARSING_to_DONE_p_sequence
|->
 ##1 RefinementVector[10]
 && !RefinementVector[12];
endproperty

DONE__pairing__INFOPARSING_to_DONE_p_sequence__2__10_12_a: assert property (disable iff(rst) DONE__pairing__INFOPARSING_to_DONE_p_sequence__2__10_12);
property DONE__pairing__INFOPARSING_to_DONE_p_sequence__2__10_12;
 INFOPARSING_to_DONE_p_sequence
|->
 ##1 !RefinementVector[10]
 && RefinementVector[12];
endproperty

DONE__pairing__INFOPARSING_to_DONE_p_sequence__3__10_12_a: assert property (disable iff(rst) DONE__pairing__INFOPARSING_to_DONE_p_sequence__3__10_12);
property DONE__pairing__INFOPARSING_to_DONE_p_sequence__3__10_12;
 INFOPARSING_to_DONE_p_sequence
|->
 ##1 RefinementVector[10]
 && RefinementVector[12];
endproperty

//INFOPARSING_to_DONE_p_sequence
//pair: {12,14}
DONE__pairing__INFOPARSING_to_DONE_p_sequence__0__12_14_a: assert property (disable iff(rst) DONE__pairing__INFOPARSING_to_DONE_p_sequence__0__12_14);
property DONE__pairing__INFOPARSING_to_DONE_p_sequence__0__12_14;
 INFOPARSING_to_DONE_p_sequence
|->
 ##1 !RefinementVector[12]
 && !RefinementVector[14];
endproperty

DONE__pairing__INFOPARSING_to_DONE_p_sequence__1__12_14_a: assert property (disable iff(rst) DONE__pairing__INFOPARSING_to_DONE_p_sequence__1__12_14);
property DONE__pairing__INFOPARSING_to_DONE_p_sequence__1__12_14;
 INFOPARSING_to_DONE_p_sequence
|->
 ##1 RefinementVector[12]
 && !RefinementVector[14];
endproperty

DONE__pairing__INFOPARSING_to_DONE_p_sequence__2__12_14_a: assert property (disable iff(rst) DONE__pairing__INFOPARSING_to_DONE_p_sequence__2__12_14);
property DONE__pairing__INFOPARSING_to_DONE_p_sequence__2__12_14;
 INFOPARSING_to_DONE_p_sequence
|->
 ##1 !RefinementVector[12]
 && RefinementVector[14];
endproperty

DONE__pairing__INFOPARSING_to_DONE_p_sequence__3__12_14_a: assert property (disable iff(rst) DONE__pairing__INFOPARSING_to_DONE_p_sequence__3__12_14);
property DONE__pairing__INFOPARSING_to_DONE_p_sequence__3__12_14;
 INFOPARSING_to_DONE_p_sequence
|->
 ##1 RefinementVector[12]
 && RefinementVector[14];
endproperty


//STARTPARSING_to_DONE_p_sequence
//pair: {0,1}
DONE__pairing__STARTPARSING_to_DONE_p_sequence__0__0_1_a: assert property (disable iff(rst) DONE__pairing__STARTPARSING_to_DONE_p_sequence__0__0_1);
property DONE__pairing__STARTPARSING_to_DONE_p_sequence__0__0_1;
 STARTPARSING_to_DONE_p_sequence
|->
 ##1 !RefinementVector[0]
 && !RefinementVector[1];
endproperty

DONE__pairing__STARTPARSING_to_DONE_p_sequence__1__0_1_a: assert property (disable iff(rst) DONE__pairing__STARTPARSING_to_DONE_p_sequence__1__0_1);
property DONE__pairing__STARTPARSING_to_DONE_p_sequence__1__0_1;
 STARTPARSING_to_DONE_p_sequence
|->
 ##1 RefinementVector[0]
 && !RefinementVector[1];
endproperty

DONE__pairing__STARTPARSING_to_DONE_p_sequence__2__0_1_a: assert property (disable iff(rst) DONE__pairing__STARTPARSING_to_DONE_p_sequence__2__0_1);
property DONE__pairing__STARTPARSING_to_DONE_p_sequence__2__0_1;
 STARTPARSING_to_DONE_p_sequence
|->
 ##1 !RefinementVector[0]
 && RefinementVector[1];
endproperty

DONE__pairing__STARTPARSING_to_DONE_p_sequence__3__0_1_a: assert property (disable iff(rst) DONE__pairing__STARTPARSING_to_DONE_p_sequence__3__0_1);
property DONE__pairing__STARTPARSING_to_DONE_p_sequence__3__0_1;
 STARTPARSING_to_DONE_p_sequence
|->
 ##1 RefinementVector[0]
 && RefinementVector[1];
endproperty

//STARTPARSING_to_DONE_p_sequence
//pair: {1,5}
DONE__pairing__STARTPARSING_to_DONE_p_sequence__0__1_5_a: assert property (disable iff(rst) DONE__pairing__STARTPARSING_to_DONE_p_sequence__0__1_5);
property DONE__pairing__STARTPARSING_to_DONE_p_sequence__0__1_5;
 STARTPARSING_to_DONE_p_sequence
|->
 ##1 !RefinementVector[1]
 && !RefinementVector[5];
endproperty

DONE__pairing__STARTPARSING_to_DONE_p_sequence__1__1_5_a: assert property (disable iff(rst) DONE__pairing__STARTPARSING_to_DONE_p_sequence__1__1_5);
property DONE__pairing__STARTPARSING_to_DONE_p_sequence__1__1_5;
 STARTPARSING_to_DONE_p_sequence
|->
 ##1 RefinementVector[1]
 && !RefinementVector[5];
endproperty

DONE__pairing__STARTPARSING_to_DONE_p_sequence__2__1_5_a: assert property (disable iff(rst) DONE__pairing__STARTPARSING_to_DONE_p_sequence__2__1_5);
property DONE__pairing__STARTPARSING_to_DONE_p_sequence__2__1_5;
 STARTPARSING_to_DONE_p_sequence
|->
 ##1 !RefinementVector[1]
 && RefinementVector[5];
endproperty

DONE__pairing__STARTPARSING_to_DONE_p_sequence__3__1_5_a: assert property (disable iff(rst) DONE__pairing__STARTPARSING_to_DONE_p_sequence__3__1_5);
property DONE__pairing__STARTPARSING_to_DONE_p_sequence__3__1_5;
 STARTPARSING_to_DONE_p_sequence
|->
 ##1 RefinementVector[1]
 && RefinementVector[5];
endproperty

//STARTPARSING_to_DONE_p_sequence
//pair: {5,6}
DONE__pairing__STARTPARSING_to_DONE_p_sequence__0__5_6_a: assert property (disable iff(rst) DONE__pairing__STARTPARSING_to_DONE_p_sequence__0__5_6);
property DONE__pairing__STARTPARSING_to_DONE_p_sequence__0__5_6;
 STARTPARSING_to_DONE_p_sequence
|->
 ##1 !RefinementVector[5]
 && !RefinementVector[6];
endproperty

DONE__pairing__STARTPARSING_to_DONE_p_sequence__1__5_6_a: assert property (disable iff(rst) DONE__pairing__STARTPARSING_to_DONE_p_sequence__1__5_6);
property DONE__pairing__STARTPARSING_to_DONE_p_sequence__1__5_6;
 STARTPARSING_to_DONE_p_sequence
|->
 ##1 RefinementVector[5]
 && !RefinementVector[6];
endproperty

DONE__pairing__STARTPARSING_to_DONE_p_sequence__2__5_6_a: assert property (disable iff(rst) DONE__pairing__STARTPARSING_to_DONE_p_sequence__2__5_6);
property DONE__pairing__STARTPARSING_to_DONE_p_sequence__2__5_6;
 STARTPARSING_to_DONE_p_sequence
|->
 ##1 !RefinementVector[5]
 && RefinementVector[6];
endproperty

DONE__pairing__STARTPARSING_to_DONE_p_sequence__3__5_6_a: assert property (disable iff(rst) DONE__pairing__STARTPARSING_to_DONE_p_sequence__3__5_6);
property DONE__pairing__STARTPARSING_to_DONE_p_sequence__3__5_6;
 STARTPARSING_to_DONE_p_sequence
|->
 ##1 RefinementVector[5]
 && RefinementVector[6];
endproperty

//STARTPARSING_to_DONE_p_sequence
//pair: {6,10}
DONE__pairing__STARTPARSING_to_DONE_p_sequence__0__6_10_a: assert property (disable iff(rst) DONE__pairing__STARTPARSING_to_DONE_p_sequence__0__6_10);
property DONE__pairing__STARTPARSING_to_DONE_p_sequence__0__6_10;
 STARTPARSING_to_DONE_p_sequence
|->
 ##1 !RefinementVector[6]
 && !RefinementVector[10];
endproperty

DONE__pairing__STARTPARSING_to_DONE_p_sequence__1__6_10_a: assert property (disable iff(rst) DONE__pairing__STARTPARSING_to_DONE_p_sequence__1__6_10);
property DONE__pairing__STARTPARSING_to_DONE_p_sequence__1__6_10;
 STARTPARSING_to_DONE_p_sequence
|->
 ##1 RefinementVector[6]
 && !RefinementVector[10];
endproperty

DONE__pairing__STARTPARSING_to_DONE_p_sequence__2__6_10_a: assert property (disable iff(rst) DONE__pairing__STARTPARSING_to_DONE_p_sequence__2__6_10);
property DONE__pairing__STARTPARSING_to_DONE_p_sequence__2__6_10;
 STARTPARSING_to_DONE_p_sequence
|->
 ##1 !RefinementVector[6]
 && RefinementVector[10];
endproperty

DONE__pairing__STARTPARSING_to_DONE_p_sequence__3__6_10_a: assert property (disable iff(rst) DONE__pairing__STARTPARSING_to_DONE_p_sequence__3__6_10);
property DONE__pairing__STARTPARSING_to_DONE_p_sequence__3__6_10;
 STARTPARSING_to_DONE_p_sequence
|->
 ##1 RefinementVector[6]
 && RefinementVector[10];
endproperty



/*******************************************/
/* ENDPARSING state bit-pairing properties */
/*******************************************/

//DATAPARSING_to_ENDPARSING_p_sequence
//pair: {0,2}
ENDPARSING__pairing__DATAPARSING_to_ENDPARSING_p_sequence__0__0_2_a: assert property (disable iff(rst) ENDPARSING__pairing__DATAPARSING_to_ENDPARSING_p_sequence__0__0_2);
property ENDPARSING__pairing__DATAPARSING_to_ENDPARSING_p_sequence__0__0_2;
 DATAPARSING_to_ENDPARSING_p_sequence
|->
 ##1 !RefinementVector[0]
 && !RefinementVector[2];
endproperty

ENDPARSING__pairing__DATAPARSING_to_ENDPARSING_p_sequence__1__0_2_a: assert property (disable iff(rst) ENDPARSING__pairing__DATAPARSING_to_ENDPARSING_p_sequence__1__0_2);
property ENDPARSING__pairing__DATAPARSING_to_ENDPARSING_p_sequence__1__0_2;
 DATAPARSING_to_ENDPARSING_p_sequence
|->
 ##1 RefinementVector[0]
 && !RefinementVector[2];
endproperty

ENDPARSING__pairing__DATAPARSING_to_ENDPARSING_p_sequence__2__0_2_a: assert property (disable iff(rst) ENDPARSING__pairing__DATAPARSING_to_ENDPARSING_p_sequence__2__0_2);
property ENDPARSING__pairing__DATAPARSING_to_ENDPARSING_p_sequence__2__0_2;
 DATAPARSING_to_ENDPARSING_p_sequence
|->
 ##1 !RefinementVector[0]
 && RefinementVector[2];
endproperty

ENDPARSING__pairing__DATAPARSING_to_ENDPARSING_p_sequence__3__0_2_a: assert property (disable iff(rst) ENDPARSING__pairing__DATAPARSING_to_ENDPARSING_p_sequence__3__0_2);
property ENDPARSING__pairing__DATAPARSING_to_ENDPARSING_p_sequence__3__0_2;
 DATAPARSING_to_ENDPARSING_p_sequence
|->
 ##1 RefinementVector[0]
 && RefinementVector[2];
endproperty

//DATAPARSING_to_ENDPARSING_p_sequence
//pair: {2,10}
ENDPARSING__pairing__DATAPARSING_to_ENDPARSING_p_sequence__0__2_10_a: assert property (disable iff(rst) ENDPARSING__pairing__DATAPARSING_to_ENDPARSING_p_sequence__0__2_10);
property ENDPARSING__pairing__DATAPARSING_to_ENDPARSING_p_sequence__0__2_10;
 DATAPARSING_to_ENDPARSING_p_sequence
|->
 ##1 !RefinementVector[2]
 && !RefinementVector[10];
endproperty

ENDPARSING__pairing__DATAPARSING_to_ENDPARSING_p_sequence__1__2_10_a: assert property (disable iff(rst) ENDPARSING__pairing__DATAPARSING_to_ENDPARSING_p_sequence__1__2_10);
property ENDPARSING__pairing__DATAPARSING_to_ENDPARSING_p_sequence__1__2_10;
 DATAPARSING_to_ENDPARSING_p_sequence
|->
 ##1 RefinementVector[2]
 && !RefinementVector[10];
endproperty

ENDPARSING__pairing__DATAPARSING_to_ENDPARSING_p_sequence__2__2_10_a: assert property (disable iff(rst) ENDPARSING__pairing__DATAPARSING_to_ENDPARSING_p_sequence__2__2_10);
property ENDPARSING__pairing__DATAPARSING_to_ENDPARSING_p_sequence__2__2_10;
 DATAPARSING_to_ENDPARSING_p_sequence
|->
 ##1 !RefinementVector[2]
 && RefinementVector[10];
endproperty

ENDPARSING__pairing__DATAPARSING_to_ENDPARSING_p_sequence__3__2_10_a: assert property (disable iff(rst) ENDPARSING__pairing__DATAPARSING_to_ENDPARSING_p_sequence__3__2_10);
property ENDPARSING__pairing__DATAPARSING_to_ENDPARSING_p_sequence__3__2_10;
 DATAPARSING_to_ENDPARSING_p_sequence
|->
 ##1 RefinementVector[2]
 && RefinementVector[10];
endproperty


//INFOPARSING_to_ENDPARSING_p_sequence
//pair: {0,2}
ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__0__0_2_a: assert property (disable iff(rst) ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__0__0_2);
property ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__0__0_2;
 INFOPARSING_to_ENDPARSING_p_sequence
|->
 ##1 !RefinementVector[0]
 && !RefinementVector[2];
endproperty

ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__1__0_2_a: assert property (disable iff(rst) ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__1__0_2);
property ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__1__0_2;
 INFOPARSING_to_ENDPARSING_p_sequence
|->
 ##1 RefinementVector[0]
 && !RefinementVector[2];
endproperty

ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__2__0_2_a: assert property (disable iff(rst) ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__2__0_2);
property ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__2__0_2;
 INFOPARSING_to_ENDPARSING_p_sequence
|->
 ##1 !RefinementVector[0]
 && RefinementVector[2];
endproperty

ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__3__0_2_a: assert property (disable iff(rst) ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__3__0_2);
property ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__3__0_2;
 INFOPARSING_to_ENDPARSING_p_sequence
|->
 ##1 RefinementVector[0]
 && RefinementVector[2];
endproperty

//INFOPARSING_to_ENDPARSING_p_sequence
//pair: {2,3}
ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__0__2_3_a: assert property (disable iff(rst) ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__0__2_3);
property ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__0__2_3;
 INFOPARSING_to_ENDPARSING_p_sequence
|->
 ##1 !RefinementVector[2]
 && !RefinementVector[3];
endproperty

ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__1__2_3_a: assert property (disable iff(rst) ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__1__2_3);
property ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__1__2_3;
 INFOPARSING_to_ENDPARSING_p_sequence
|->
 ##1 RefinementVector[2]
 && !RefinementVector[3];
endproperty

ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__2__2_3_a: assert property (disable iff(rst) ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__2__2_3);
property ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__2__2_3;
 INFOPARSING_to_ENDPARSING_p_sequence
|->
 ##1 !RefinementVector[2]
 && RefinementVector[3];
endproperty

ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__3__2_3_a: assert property (disable iff(rst) ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__3__2_3);
property ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__3__2_3;
 INFOPARSING_to_ENDPARSING_p_sequence
|->
 ##1 RefinementVector[2]
 && RefinementVector[3];
endproperty

//INFOPARSING_to_ENDPARSING_p_sequence
//pair: {3,10}
ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__0__3_10_a: assert property (disable iff(rst) ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__0__3_10);
property ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__0__3_10;
 INFOPARSING_to_ENDPARSING_p_sequence
|->
 ##1 !RefinementVector[3]
 && !RefinementVector[10];
endproperty

ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__1__3_10_a: assert property (disable iff(rst) ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__1__3_10);
property ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__1__3_10;
 INFOPARSING_to_ENDPARSING_p_sequence
|->
 ##1 RefinementVector[3]
 && !RefinementVector[10];
endproperty

ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__2__3_10_a: assert property (disable iff(rst) ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__2__3_10);
property ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__2__3_10;
 INFOPARSING_to_ENDPARSING_p_sequence
|->
 ##1 !RefinementVector[3]
 && RefinementVector[10];
endproperty

ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__3__3_10_a: assert property (disable iff(rst) ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__3__3_10);
property ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__3__3_10;
 INFOPARSING_to_ENDPARSING_p_sequence
|->
 ##1 RefinementVector[3]
 && RefinementVector[10];
endproperty

//INFOPARSING_to_ENDPARSING_p_sequence
//pair: {10,12}
ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__0__10_12_a: assert property (disable iff(rst) ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__0__10_12);
property ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__0__10_12;
 INFOPARSING_to_ENDPARSING_p_sequence
|->
 ##1 !RefinementVector[10]
 && !RefinementVector[12];
endproperty

ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__1__10_12_a: assert property (disable iff(rst) ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__1__10_12);
property ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__1__10_12;
 INFOPARSING_to_ENDPARSING_p_sequence
|->
 ##1 RefinementVector[10]
 && !RefinementVector[12];
endproperty

ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__2__10_12_a: assert property (disable iff(rst) ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__2__10_12);
property ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__2__10_12;
 INFOPARSING_to_ENDPARSING_p_sequence
|->
 ##1 !RefinementVector[10]
 && RefinementVector[12];
endproperty

ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__3__10_12_a: assert property (disable iff(rst) ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__3__10_12);
property ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__3__10_12;
 INFOPARSING_to_ENDPARSING_p_sequence
|->
 ##1 RefinementVector[10]
 && RefinementVector[12];
endproperty

//INFOPARSING_to_ENDPARSING_p_sequence
//pair: {12,14}
ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__0__12_14_a: assert property (disable iff(rst) ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__0__12_14);
property ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__0__12_14;
 INFOPARSING_to_ENDPARSING_p_sequence
|->
 ##1 !RefinementVector[12]
 && !RefinementVector[14];
endproperty

ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__1__12_14_a: assert property (disable iff(rst) ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__1__12_14);
property ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__1__12_14;
 INFOPARSING_to_ENDPARSING_p_sequence
|->
 ##1 RefinementVector[12]
 && !RefinementVector[14];
endproperty

ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__2__12_14_a: assert property (disable iff(rst) ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__2__12_14);
property ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__2__12_14;
 INFOPARSING_to_ENDPARSING_p_sequence
|->
 ##1 !RefinementVector[12]
 && RefinementVector[14];
endproperty

ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__3__12_14_a: assert property (disable iff(rst) ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__3__12_14);
property ENDPARSING__pairing__INFOPARSING_to_ENDPARSING_p_sequence__3__12_14;
 INFOPARSING_to_ENDPARSING_p_sequence
|->
 ##1 RefinementVector[12]
 && RefinementVector[14];
endproperty


//STARTPARSING_to_ENDPARSING_p_sequence
//pair: {0,10}
ENDPARSING__pairing__STARTPARSING_to_ENDPARSING_p_sequence__0__0_10_a: assert property (disable iff(rst) ENDPARSING__pairing__STARTPARSING_to_ENDPARSING_p_sequence__0__0_10);
property ENDPARSING__pairing__STARTPARSING_to_ENDPARSING_p_sequence__0__0_10;
 STARTPARSING_to_ENDPARSING_p_sequence
|->
 ##1 !RefinementVector[0]
 && !RefinementVector[10];
endproperty

ENDPARSING__pairing__STARTPARSING_to_ENDPARSING_p_sequence__1__0_10_a: assert property (disable iff(rst) ENDPARSING__pairing__STARTPARSING_to_ENDPARSING_p_sequence__1__0_10);
property ENDPARSING__pairing__STARTPARSING_to_ENDPARSING_p_sequence__1__0_10;
 STARTPARSING_to_ENDPARSING_p_sequence
|->
 ##1 RefinementVector[0]
 && !RefinementVector[10];
endproperty

ENDPARSING__pairing__STARTPARSING_to_ENDPARSING_p_sequence__2__0_10_a: assert property (disable iff(rst) ENDPARSING__pairing__STARTPARSING_to_ENDPARSING_p_sequence__2__0_10);
property ENDPARSING__pairing__STARTPARSING_to_ENDPARSING_p_sequence__2__0_10;
 STARTPARSING_to_ENDPARSING_p_sequence
|->
 ##1 !RefinementVector[0]
 && RefinementVector[10];
endproperty

ENDPARSING__pairing__STARTPARSING_to_ENDPARSING_p_sequence__3__0_10_a: assert property (disable iff(rst) ENDPARSING__pairing__STARTPARSING_to_ENDPARSING_p_sequence__3__0_10);
property ENDPARSING__pairing__STARTPARSING_to_ENDPARSING_p_sequence__3__0_10;
 STARTPARSING_to_ENDPARSING_p_sequence
|->
 ##1 RefinementVector[0]
 && RefinementVector[10];
endproperty


/********************************************/
/* INFOPARSING state bit-pairing properties */
/********************************************/

//DATAPARSING_to_INFOPARSING_p_sequence
//pair: {0,10}
INFOPARSING__pairing__DATAPARSING_to_INFOPARSING_p_sequence__0__0_10_a: assert property (disable iff(rst) INFOPARSING__pairing__DATAPARSING_to_INFOPARSING_p_sequence__0__0_10);
property INFOPARSING__pairing__DATAPARSING_to_INFOPARSING_p_sequence__0__0_10;
 DATAPARSING_to_INFOPARSING_p_sequence
|->
 ##1 !RefinementVector[0]
 && !RefinementVector[10];
endproperty

INFOPARSING__pairing__DATAPARSING_to_INFOPARSING_p_sequence__1__0_10_a: assert property (disable iff(rst) INFOPARSING__pairing__DATAPARSING_to_INFOPARSING_p_sequence__1__0_10);
property INFOPARSING__pairing__DATAPARSING_to_INFOPARSING_p_sequence__1__0_10;
 DATAPARSING_to_INFOPARSING_p_sequence
|->
 ##1 RefinementVector[0]
 && !RefinementVector[10];
endproperty

INFOPARSING__pairing__DATAPARSING_to_INFOPARSING_p_sequence__2__0_10_a: assert property (disable iff(rst) INFOPARSING__pairing__DATAPARSING_to_INFOPARSING_p_sequence__2__0_10);
property INFOPARSING__pairing__DATAPARSING_to_INFOPARSING_p_sequence__2__0_10;
 DATAPARSING_to_INFOPARSING_p_sequence
|->
 ##1 !RefinementVector[0]
 && RefinementVector[10];
endproperty

INFOPARSING__pairing__DATAPARSING_to_INFOPARSING_p_sequence__3__0_10_a: assert property (disable iff(rst) INFOPARSING__pairing__DATAPARSING_to_INFOPARSING_p_sequence__3__0_10);
property INFOPARSING__pairing__DATAPARSING_to_INFOPARSING_p_sequence__3__0_10;
 DATAPARSING_to_INFOPARSING_p_sequence
|->
 ##1 RefinementVector[0]
 && RefinementVector[10];
endproperty


//INFOPARSING_to_INFOPARSING_1_p_sequence
//pair: {0,2}
INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__0__0_2_a: assert property (disable iff(rst) INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__0__0_2);
property INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__0__0_2;
 INFOPARSING_to_INFOPARSING_1_p_sequence
|->
 ##1 !RefinementVector[0]
 && !RefinementVector[2];
endproperty

INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__1__0_2_a: assert property (disable iff(rst) INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__1__0_2);
property INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__1__0_2;
 INFOPARSING_to_INFOPARSING_1_p_sequence
|->
 ##1 RefinementVector[0]
 && !RefinementVector[2];
endproperty

INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__2__0_2_a: assert property (disable iff(rst) INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__2__0_2);
property INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__2__0_2;
 INFOPARSING_to_INFOPARSING_1_p_sequence
|->
 ##1 !RefinementVector[0]
 && RefinementVector[2];
endproperty

INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__3__0_2_a: assert property (disable iff(rst) INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__3__0_2);
property INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__3__0_2;
 INFOPARSING_to_INFOPARSING_1_p_sequence
|->
 ##1 RefinementVector[0]
 && RefinementVector[2];
endproperty

//INFOPARSING_to_INFOPARSING_1_p_sequence
//pair: {2,3}
INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__0__2_3_a: assert property (disable iff(rst) INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__0__2_3);
property INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__0__2_3;
 INFOPARSING_to_INFOPARSING_1_p_sequence
|->
 ##1 !RefinementVector[2]
 && !RefinementVector[3];
endproperty

INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__1__2_3_a: assert property (disable iff(rst) INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__1__2_3);
property INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__1__2_3;
 INFOPARSING_to_INFOPARSING_1_p_sequence
|->
 ##1 RefinementVector[2]
 && !RefinementVector[3];
endproperty

INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__2__2_3_a: assert property (disable iff(rst) INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__2__2_3);
property INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__2__2_3;
 INFOPARSING_to_INFOPARSING_1_p_sequence
|->
 ##1 !RefinementVector[2]
 && RefinementVector[3];
endproperty

INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__3__2_3_a: assert property (disable iff(rst) INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__3__2_3);
property INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__3__2_3;
 INFOPARSING_to_INFOPARSING_1_p_sequence
|->
 ##1 RefinementVector[2]
 && RefinementVector[3];
endproperty

//INFOPARSING_to_INFOPARSING_1_p_sequence
//pair: {3,10}
INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__0__3_10_a: assert property (disable iff(rst) INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__0__3_10);
property INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__0__3_10;
 INFOPARSING_to_INFOPARSING_1_p_sequence
|->
 ##1 !RefinementVector[3]
 && !RefinementVector[10];
endproperty

INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__1__3_10_a: assert property (disable iff(rst) INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__1__3_10);
property INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__1__3_10;
 INFOPARSING_to_INFOPARSING_1_p_sequence
|->
 ##1 RefinementVector[3]
 && !RefinementVector[10];
endproperty

INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__2__3_10_a: assert property (disable iff(rst) INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__2__3_10);
property INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__2__3_10;
 INFOPARSING_to_INFOPARSING_1_p_sequence
|->
 ##1 !RefinementVector[3]
 && RefinementVector[10];
endproperty

INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__3__3_10_a: assert property (disable iff(rst) INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__3__3_10);
property INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__3__3_10;
 INFOPARSING_to_INFOPARSING_1_p_sequence
|->
 ##1 RefinementVector[3]
 && RefinementVector[10];
endproperty

//INFOPARSING_to_INFOPARSING_1_p_sequence
//pair: {10,12}
INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__0__10_12_a: assert property (disable iff(rst) INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__0__10_12);
property INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__0__10_12;
 INFOPARSING_to_INFOPARSING_1_p_sequence
|->
 ##1 !RefinementVector[10]
 && !RefinementVector[12];
endproperty

INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__1__10_12_a: assert property (disable iff(rst) INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__1__10_12);
property INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__1__10_12;
 INFOPARSING_to_INFOPARSING_1_p_sequence
|->
 ##1 RefinementVector[10]
 && !RefinementVector[12];
endproperty

INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__2__10_12_a: assert property (disable iff(rst) INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__2__10_12);
property INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__2__10_12;
 INFOPARSING_to_INFOPARSING_1_p_sequence
|->
 ##1 !RefinementVector[10]
 && RefinementVector[12];
endproperty

INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__3__10_12_a: assert property (disable iff(rst) INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__3__10_12);
property INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__3__10_12;
 INFOPARSING_to_INFOPARSING_1_p_sequence
|->
 ##1 RefinementVector[10]
 && RefinementVector[12];
endproperty

//INFOPARSING_to_INFOPARSING_1_p_sequence
//pair: {12,14}
INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__0__12_14_a: assert property (disable iff(rst) INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__0__12_14);
property INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__0__12_14;
 INFOPARSING_to_INFOPARSING_1_p_sequence
|->
 ##1 !RefinementVector[12]
 && !RefinementVector[14];
endproperty

INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__1__12_14_a: assert property (disable iff(rst) INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__1__12_14);
property INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__1__12_14;
 INFOPARSING_to_INFOPARSING_1_p_sequence
|->
 ##1 RefinementVector[12]
 && !RefinementVector[14];
endproperty

INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__2__12_14_a: assert property (disable iff(rst) INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__2__12_14);
property INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__2__12_14;
 INFOPARSING_to_INFOPARSING_1_p_sequence
|->
 ##1 !RefinementVector[12]
 && RefinementVector[14];
endproperty

INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__3__12_14_a: assert property (disable iff(rst) INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__3__12_14);
property INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_1_p_sequence__3__12_14;
 INFOPARSING_to_INFOPARSING_1_p_sequence
|->
 ##1 RefinementVector[12]
 && RefinementVector[14];
endproperty


//INFOPARSING_to_INFOPARSING_p_sequence
//pair: {0,3}
INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__0__0_3_a: assert property (disable iff(rst) INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__0__0_3);
property INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__0__0_3;
 INFOPARSING_to_INFOPARSING_p_sequence
|->
 ##1 !RefinementVector[0]
 && !RefinementVector[3];
endproperty

INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__1__0_3_a: assert property (disable iff(rst) INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__1__0_3);
property INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__1__0_3;
 INFOPARSING_to_INFOPARSING_p_sequence
|->
 ##1 RefinementVector[0]
 && !RefinementVector[3];
endproperty

INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__2__0_3_a: assert property (disable iff(rst) INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__2__0_3);
property INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__2__0_3;
 INFOPARSING_to_INFOPARSING_p_sequence
|->
 ##1 !RefinementVector[0]
 && RefinementVector[3];
endproperty

INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__3__0_3_a: assert property (disable iff(rst) INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__3__0_3);
property INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__3__0_3;
 INFOPARSING_to_INFOPARSING_p_sequence
|->
 ##1 RefinementVector[0]
 && RefinementVector[3];
endproperty

//INFOPARSING_to_INFOPARSING_p_sequence
//pair: {3,10}
INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__0__3_10_a: assert property (disable iff(rst) INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__0__3_10);
property INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__0__3_10;
 INFOPARSING_to_INFOPARSING_p_sequence
|->
 ##1 !RefinementVector[3]
 && !RefinementVector[10];
endproperty

INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__1__3_10_a: assert property (disable iff(rst) INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__1__3_10);
property INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__1__3_10;
 INFOPARSING_to_INFOPARSING_p_sequence
|->
 ##1 RefinementVector[3]
 && !RefinementVector[10];
endproperty

INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__2__3_10_a: assert property (disable iff(rst) INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__2__3_10);
property INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__2__3_10;
 INFOPARSING_to_INFOPARSING_p_sequence
|->
 ##1 !RefinementVector[3]
 && RefinementVector[10];
endproperty

INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__3__3_10_a: assert property (disable iff(rst) INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__3__3_10);
property INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__3__3_10;
 INFOPARSING_to_INFOPARSING_p_sequence
|->
 ##1 RefinementVector[3]
 && RefinementVector[10];
endproperty

//INFOPARSING_to_INFOPARSING_p_sequence
//pair: {10,12}
INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__0__10_12_a: assert property (disable iff(rst) INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__0__10_12);
property INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__0__10_12;
 INFOPARSING_to_INFOPARSING_p_sequence
|->
 ##1 !RefinementVector[10]
 && !RefinementVector[12];
endproperty

INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__1__10_12_a: assert property (disable iff(rst) INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__1__10_12);
property INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__1__10_12;
 INFOPARSING_to_INFOPARSING_p_sequence
|->
 ##1 RefinementVector[10]
 && !RefinementVector[12];
endproperty

INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__2__10_12_a: assert property (disable iff(rst) INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__2__10_12);
property INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__2__10_12;
 INFOPARSING_to_INFOPARSING_p_sequence
|->
 ##1 !RefinementVector[10]
 && RefinementVector[12];
endproperty

INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__3__10_12_a: assert property (disable iff(rst) INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__3__10_12);
property INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__3__10_12;
 INFOPARSING_to_INFOPARSING_p_sequence
|->
 ##1 RefinementVector[10]
 && RefinementVector[12];
endproperty

//INFOPARSING_to_INFOPARSING_p_sequence
//pair: {12,14}
INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__0__12_14_a: assert property (disable iff(rst) INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__0__12_14);
property INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__0__12_14;
 INFOPARSING_to_INFOPARSING_p_sequence
|->
 ##1 !RefinementVector[12]
 && !RefinementVector[14];
endproperty

INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__1__12_14_a: assert property (disable iff(rst) INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__1__12_14);
property INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__1__12_14;
 INFOPARSING_to_INFOPARSING_p_sequence
|->
 ##1 RefinementVector[12]
 && !RefinementVector[14];
endproperty

INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__2__12_14_a: assert property (disable iff(rst) INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__2__12_14);
property INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__2__12_14;
 INFOPARSING_to_INFOPARSING_p_sequence
|->
 ##1 !RefinementVector[12]
 && RefinementVector[14];
endproperty

INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__3__12_14_a: assert property (disable iff(rst) INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__3__12_14);
property INFOPARSING__pairing__INFOPARSING_to_INFOPARSING_p_sequence__3__12_14;
 INFOPARSING_to_INFOPARSING_p_sequence
|->
 ##1 RefinementVector[12]
 && RefinementVector[14];
endproperty


//STARTPARSING_to_INFOPARSING_p_sequence
//pair: {0,10}
INFOPARSING__pairing__STARTPARSING_to_INFOPARSING_p_sequence__0__0_10_a: assert property (disable iff(rst) INFOPARSING__pairing__STARTPARSING_to_INFOPARSING_p_sequence__0__0_10);
property INFOPARSING__pairing__STARTPARSING_to_INFOPARSING_p_sequence__0__0_10;
 STARTPARSING_to_INFOPARSING_p_sequence
|->
 ##1 !RefinementVector[0]
 && !RefinementVector[10];
endproperty

INFOPARSING__pairing__STARTPARSING_to_INFOPARSING_p_sequence__1__0_10_a: assert property (disable iff(rst) INFOPARSING__pairing__STARTPARSING_to_INFOPARSING_p_sequence__1__0_10);
property INFOPARSING__pairing__STARTPARSING_to_INFOPARSING_p_sequence__1__0_10;
 STARTPARSING_to_INFOPARSING_p_sequence
|->
 ##1 RefinementVector[0]
 && !RefinementVector[10];
endproperty

INFOPARSING__pairing__STARTPARSING_to_INFOPARSING_p_sequence__2__0_10_a: assert property (disable iff(rst) INFOPARSING__pairing__STARTPARSING_to_INFOPARSING_p_sequence__2__0_10);
property INFOPARSING__pairing__STARTPARSING_to_INFOPARSING_p_sequence__2__0_10;
 STARTPARSING_to_INFOPARSING_p_sequence
|->
 ##1 !RefinementVector[0]
 && RefinementVector[10];
endproperty

INFOPARSING__pairing__STARTPARSING_to_INFOPARSING_p_sequence__3__0_10_a: assert property (disable iff(rst) INFOPARSING__pairing__STARTPARSING_to_INFOPARSING_p_sequence__3__0_10);
property INFOPARSING__pairing__STARTPARSING_to_INFOPARSING_p_sequence__3__0_10;
 STARTPARSING_to_INFOPARSING_p_sequence
|->
 ##1 RefinementVector[0]
 && RefinementVector[10];
endproperty


/**************************************/
/* READY state bit-pairing properties */
/**************************************/


//DONE_to_READY_p_sequence
//pair: {0,1}
READY__pairing__DONE_to_READY_p_sequence__0__0_1_a: assert property (disable iff(rst) READY__pairing__DONE_to_READY_p_sequence__0__0_1);
property READY__pairing__DONE_to_READY_p_sequence__0__0_1;
 DONE_to_READY_p_sequence
|->
 ##1 !RefinementVector[0]
 && !RefinementVector[1];
endproperty

READY__pairing__DONE_to_READY_p_sequence__1__0_1_a: assert property (disable iff(rst) READY__pairing__DONE_to_READY_p_sequence__1__0_1);
property READY__pairing__DONE_to_READY_p_sequence__1__0_1;
 DONE_to_READY_p_sequence
|->
 ##1 RefinementVector[0]
 && !RefinementVector[1];
endproperty

READY__pairing__DONE_to_READY_p_sequence__2__0_1_a: assert property (disable iff(rst) READY__pairing__DONE_to_READY_p_sequence__2__0_1);
property READY__pairing__DONE_to_READY_p_sequence__2__0_1;
 DONE_to_READY_p_sequence
|->
 ##1 !RefinementVector[0]
 && RefinementVector[1];
endproperty

READY__pairing__DONE_to_READY_p_sequence__3__0_1_a: assert property (disable iff(rst) READY__pairing__DONE_to_READY_p_sequence__3__0_1);
property READY__pairing__DONE_to_READY_p_sequence__3__0_1;
 DONE_to_READY_p_sequence
|->
 ##1 RefinementVector[0]
 && RefinementVector[1];
endproperty

//DONE_to_READY_p_sequence
//pair: {1,2}
READY__pairing__DONE_to_READY_p_sequence__0__1_2_a: assert property (disable iff(rst) READY__pairing__DONE_to_READY_p_sequence__0__1_2);
property READY__pairing__DONE_to_READY_p_sequence__0__1_2;
 DONE_to_READY_p_sequence
|->
 ##1 !RefinementVector[1]
 && !RefinementVector[2];
endproperty

READY__pairing__DONE_to_READY_p_sequence__1__1_2_a: assert property (disable iff(rst) READY__pairing__DONE_to_READY_p_sequence__1__1_2);
property READY__pairing__DONE_to_READY_p_sequence__1__1_2;
 DONE_to_READY_p_sequence
|->
 ##1 RefinementVector[1]
 && !RefinementVector[2];
endproperty

READY__pairing__DONE_to_READY_p_sequence__2__1_2_a: assert property (disable iff(rst) READY__pairing__DONE_to_READY_p_sequence__2__1_2);
property READY__pairing__DONE_to_READY_p_sequence__2__1_2;
 DONE_to_READY_p_sequence
|->
 ##1 !RefinementVector[1]
 && RefinementVector[2];
endproperty

READY__pairing__DONE_to_READY_p_sequence__3__1_2_a: assert property (disable iff(rst) READY__pairing__DONE_to_READY_p_sequence__3__1_2);
property READY__pairing__DONE_to_READY_p_sequence__3__1_2;
 DONE_to_READY_p_sequence
|->
 ##1 RefinementVector[1]
 && RefinementVector[2];
endproperty

//DONE_to_READY_p_sequence
//pair: {2,3}
READY__pairing__DONE_to_READY_p_sequence__0__2_3_a: assert property (disable iff(rst) READY__pairing__DONE_to_READY_p_sequence__0__2_3);
property READY__pairing__DONE_to_READY_p_sequence__0__2_3;
 DONE_to_READY_p_sequence
|->
 ##1 !RefinementVector[2]
 && !RefinementVector[3];
endproperty

READY__pairing__DONE_to_READY_p_sequence__1__2_3_a: assert property (disable iff(rst) READY__pairing__DONE_to_READY_p_sequence__1__2_3);
property READY__pairing__DONE_to_READY_p_sequence__1__2_3;
 DONE_to_READY_p_sequence
|->
 ##1 RefinementVector[2]
 && !RefinementVector[3];
endproperty

READY__pairing__DONE_to_READY_p_sequence__2__2_3_a: assert property (disable iff(rst) READY__pairing__DONE_to_READY_p_sequence__2__2_3);
property READY__pairing__DONE_to_READY_p_sequence__2__2_3;
 DONE_to_READY_p_sequence
|->
 ##1 !RefinementVector[2]
 && RefinementVector[3];
endproperty

READY__pairing__DONE_to_READY_p_sequence__3__2_3_a: assert property (disable iff(rst) READY__pairing__DONE_to_READY_p_sequence__3__2_3);
property READY__pairing__DONE_to_READY_p_sequence__3__2_3;
 DONE_to_READY_p_sequence
|->
 ##1 RefinementVector[2]
 && RefinementVector[3];
endproperty

//DONE_to_READY_p_sequence
//pair: {3,4}
READY__pairing__DONE_to_READY_p_sequence__0__3_4_a: assert property (disable iff(rst) READY__pairing__DONE_to_READY_p_sequence__0__3_4);
property READY__pairing__DONE_to_READY_p_sequence__0__3_4;
 DONE_to_READY_p_sequence
|->
 ##1 !RefinementVector[3]
 && !RefinementVector[4];
endproperty

READY__pairing__DONE_to_READY_p_sequence__1__3_4_a: assert property (disable iff(rst) READY__pairing__DONE_to_READY_p_sequence__1__3_4);
property READY__pairing__DONE_to_READY_p_sequence__1__3_4;
 DONE_to_READY_p_sequence
|->
 ##1 RefinementVector[3]
 && !RefinementVector[4];
endproperty

READY__pairing__DONE_to_READY_p_sequence__2__3_4_a: assert property (disable iff(rst) READY__pairing__DONE_to_READY_p_sequence__2__3_4);
property READY__pairing__DONE_to_READY_p_sequence__2__3_4;
 DONE_to_READY_p_sequence
|->
 ##1 !RefinementVector[3]
 && RefinementVector[4];
endproperty

READY__pairing__DONE_to_READY_p_sequence__3__3_4_a: assert property (disable iff(rst) READY__pairing__DONE_to_READY_p_sequence__3__3_4);
property READY__pairing__DONE_to_READY_p_sequence__3__3_4;
 DONE_to_READY_p_sequence
|->
 ##1 RefinementVector[3]
 && RefinementVector[4];
endproperty

//DONE_to_READY_p_sequence
//pair: {4,5}
READY__pairing__DONE_to_READY_p_sequence__0__4_5_a: assert property (disable iff(rst) READY__pairing__DONE_to_READY_p_sequence__0__4_5);
property READY__pairing__DONE_to_READY_p_sequence__0__4_5;
 DONE_to_READY_p_sequence
|->
 ##1 !RefinementVector[4]
 && !RefinementVector[5];
endproperty

READY__pairing__DONE_to_READY_p_sequence__1__4_5_a: assert property (disable iff(rst) READY__pairing__DONE_to_READY_p_sequence__1__4_5);
property READY__pairing__DONE_to_READY_p_sequence__1__4_5;
 DONE_to_READY_p_sequence
|->
 ##1 RefinementVector[4]
 && !RefinementVector[5];
endproperty

READY__pairing__DONE_to_READY_p_sequence__2__4_5_a: assert property (disable iff(rst) READY__pairing__DONE_to_READY_p_sequence__2__4_5);
property READY__pairing__DONE_to_READY_p_sequence__2__4_5;
 DONE_to_READY_p_sequence
|->
 ##1 !RefinementVector[4]
 && RefinementVector[5];
endproperty

READY__pairing__DONE_to_READY_p_sequence__3__4_5_a: assert property (disable iff(rst) READY__pairing__DONE_to_READY_p_sequence__3__4_5);
property READY__pairing__DONE_to_READY_p_sequence__3__4_5;
 DONE_to_READY_p_sequence
|->
 ##1 RefinementVector[4]
 && RefinementVector[5];
endproperty

//DONE_to_READY_p_sequence
//pair: {5,6}
READY__pairing__DONE_to_READY_p_sequence__0__5_6_a: assert property (disable iff(rst) READY__pairing__DONE_to_READY_p_sequence__0__5_6);
property READY__pairing__DONE_to_READY_p_sequence__0__5_6;
 DONE_to_READY_p_sequence
|->
 ##1 !RefinementVector[5]
 && !RefinementVector[6];
endproperty

READY__pairing__DONE_to_READY_p_sequence__1__5_6_a: assert property (disable iff(rst) READY__pairing__DONE_to_READY_p_sequence__1__5_6);
property READY__pairing__DONE_to_READY_p_sequence__1__5_6;
 DONE_to_READY_p_sequence
|->
 ##1 RefinementVector[5]
 && !RefinementVector[6];
endproperty

READY__pairing__DONE_to_READY_p_sequence__2__5_6_a: assert property (disable iff(rst) READY__pairing__DONE_to_READY_p_sequence__2__5_6);
property READY__pairing__DONE_to_READY_p_sequence__2__5_6;
 DONE_to_READY_p_sequence
|->
 ##1 !RefinementVector[5]
 && RefinementVector[6];
endproperty

READY__pairing__DONE_to_READY_p_sequence__3__5_6_a: assert property (disable iff(rst) READY__pairing__DONE_to_READY_p_sequence__3__5_6);
property READY__pairing__DONE_to_READY_p_sequence__3__5_6;
 DONE_to_READY_p_sequence
|->
 ##1 RefinementVector[5]
 && RefinementVector[6];
endproperty

//DONE_to_READY_p_sequence
//pair: {6,10}
READY__pairing__DONE_to_READY_p_sequence__0__6_10_a: assert property (disable iff(rst) READY__pairing__DONE_to_READY_p_sequence__0__6_10);
property READY__pairing__DONE_to_READY_p_sequence__0__6_10;
 DONE_to_READY_p_sequence
|->
 ##1 !RefinementVector[6]
 && !RefinementVector[10];
endproperty

READY__pairing__DONE_to_READY_p_sequence__1__6_10_a: assert property (disable iff(rst) READY__pairing__DONE_to_READY_p_sequence__1__6_10);
property READY__pairing__DONE_to_READY_p_sequence__1__6_10;
 DONE_to_READY_p_sequence
|->
 ##1 RefinementVector[6]
 && !RefinementVector[10];
endproperty

READY__pairing__DONE_to_READY_p_sequence__2__6_10_a: assert property (disable iff(rst) READY__pairing__DONE_to_READY_p_sequence__2__6_10);
property READY__pairing__DONE_to_READY_p_sequence__2__6_10;
 DONE_to_READY_p_sequence
|->
 ##1 !RefinementVector[6]
 && RefinementVector[10];
endproperty

READY__pairing__DONE_to_READY_p_sequence__3__6_10_a: assert property (disable iff(rst) READY__pairing__DONE_to_READY_p_sequence__3__6_10);
property READY__pairing__DONE_to_READY_p_sequence__3__6_10;
 DONE_to_READY_p_sequence
|->
 ##1 RefinementVector[6]
 && RefinementVector[10];
endproperty

//DONE_to_READY_p_sequence
//pair: {10,12}
READY__pairing__DONE_to_READY_p_sequence__0__10_12_a: assert property (disable iff(rst) READY__pairing__DONE_to_READY_p_sequence__0__10_12);
property READY__pairing__DONE_to_READY_p_sequence__0__10_12;
 DONE_to_READY_p_sequence
|->
 ##1 !RefinementVector[10]
 && !RefinementVector[12];
endproperty

READY__pairing__DONE_to_READY_p_sequence__1__10_12_a: assert property (disable iff(rst) READY__pairing__DONE_to_READY_p_sequence__1__10_12);
property READY__pairing__DONE_to_READY_p_sequence__1__10_12;
 DONE_to_READY_p_sequence
|->
 ##1 RefinementVector[10]
 && !RefinementVector[12];
endproperty

READY__pairing__DONE_to_READY_p_sequence__2__10_12_a: assert property (disable iff(rst) READY__pairing__DONE_to_READY_p_sequence__2__10_12);
property READY__pairing__DONE_to_READY_p_sequence__2__10_12;
 DONE_to_READY_p_sequence
|->
 ##1 !RefinementVector[10]
 && RefinementVector[12];
endproperty

READY__pairing__DONE_to_READY_p_sequence__3__10_12_a: assert property (disable iff(rst) READY__pairing__DONE_to_READY_p_sequence__3__10_12);
property READY__pairing__DONE_to_READY_p_sequence__3__10_12;
 DONE_to_READY_p_sequence
|->
 ##1 RefinementVector[10]
 && RefinementVector[12];
endproperty

//DONE_to_READY_p_sequence
//pair: {12,14}
READY__pairing__DONE_to_READY_p_sequence__0__12_14_a: assert property (disable iff(rst) READY__pairing__DONE_to_READY_p_sequence__0__12_14);
property READY__pairing__DONE_to_READY_p_sequence__0__12_14;
 DONE_to_READY_p_sequence
|->
 ##1 !RefinementVector[12]
 && !RefinementVector[14];
endproperty

READY__pairing__DONE_to_READY_p_sequence__1__12_14_a: assert property (disable iff(rst) READY__pairing__DONE_to_READY_p_sequence__1__12_14);
property READY__pairing__DONE_to_READY_p_sequence__1__12_14;
 DONE_to_READY_p_sequence
|->
 ##1 RefinementVector[12]
 && !RefinementVector[14];
endproperty

READY__pairing__DONE_to_READY_p_sequence__2__12_14_a: assert property (disable iff(rst) READY__pairing__DONE_to_READY_p_sequence__2__12_14);
property READY__pairing__DONE_to_READY_p_sequence__2__12_14;
 DONE_to_READY_p_sequence
|->
 ##1 !RefinementVector[12]
 && RefinementVector[14];
endproperty

READY__pairing__DONE_to_READY_p_sequence__3__12_14_a: assert property (disable iff(rst) READY__pairing__DONE_to_READY_p_sequence__3__12_14);
property READY__pairing__DONE_to_READY_p_sequence__3__12_14;
 DONE_to_READY_p_sequence
|->
 ##1 RefinementVector[12]
 && RefinementVector[14];
endproperty


//READY_wait_p_sequence
//pair: {0,1}
READY__pairing__READY_wait_p_sequence__0__0_1_a: assert property (disable iff(rst) READY__pairing__READY_wait_p_sequence__0__0_1);
property READY__pairing__READY_wait_p_sequence__0__0_1;
 READY_wait_p_sequence
|->
 ##1 !RefinementVector[0]
 && !RefinementVector[1];
endproperty

READY__pairing__READY_wait_p_sequence__1__0_1_a: assert property (disable iff(rst) READY__pairing__READY_wait_p_sequence__1__0_1);
property READY__pairing__READY_wait_p_sequence__1__0_1;
 READY_wait_p_sequence
|->
 ##1 RefinementVector[0]
 && !RefinementVector[1];
endproperty

READY__pairing__READY_wait_p_sequence__2__0_1_a: assert property (disable iff(rst) READY__pairing__READY_wait_p_sequence__2__0_1);
property READY__pairing__READY_wait_p_sequence__2__0_1;
 READY_wait_p_sequence
|->
 ##1 !RefinementVector[0]
 && RefinementVector[1];
endproperty

READY__pairing__READY_wait_p_sequence__3__0_1_a: assert property (disable iff(rst) READY__pairing__READY_wait_p_sequence__3__0_1);
property READY__pairing__READY_wait_p_sequence__3__0_1;
 READY_wait_p_sequence
|->
 ##1 RefinementVector[0]
 && RefinementVector[1];
endproperty

//READY_wait_p_sequence
//pair: {1,2}
READY__pairing__READY_wait_p_sequence__0__1_2_a: assert property (disable iff(rst) READY__pairing__READY_wait_p_sequence__0__1_2);
property READY__pairing__READY_wait_p_sequence__0__1_2;
 READY_wait_p_sequence
|->
 ##1 !RefinementVector[1]
 && !RefinementVector[2];
endproperty

READY__pairing__READY_wait_p_sequence__1__1_2_a: assert property (disable iff(rst) READY__pairing__READY_wait_p_sequence__1__1_2);
property READY__pairing__READY_wait_p_sequence__1__1_2;
 READY_wait_p_sequence
|->
 ##1 RefinementVector[1]
 && !RefinementVector[2];
endproperty

READY__pairing__READY_wait_p_sequence__2__1_2_a: assert property (disable iff(rst) READY__pairing__READY_wait_p_sequence__2__1_2);
property READY__pairing__READY_wait_p_sequence__2__1_2;
 READY_wait_p_sequence
|->
 ##1 !RefinementVector[1]
 && RefinementVector[2];
endproperty

READY__pairing__READY_wait_p_sequence__3__1_2_a: assert property (disable iff(rst) READY__pairing__READY_wait_p_sequence__3__1_2);
property READY__pairing__READY_wait_p_sequence__3__1_2;
 READY_wait_p_sequence
|->
 ##1 RefinementVector[1]
 && RefinementVector[2];
endproperty

//READY_wait_p_sequence
//pair: {2,3}
READY__pairing__READY_wait_p_sequence__0__2_3_a: assert property (disable iff(rst) READY__pairing__READY_wait_p_sequence__0__2_3);
property READY__pairing__READY_wait_p_sequence__0__2_3;
 READY_wait_p_sequence
|->
 ##1 !RefinementVector[2]
 && !RefinementVector[3];
endproperty

READY__pairing__READY_wait_p_sequence__1__2_3_a: assert property (disable iff(rst) READY__pairing__READY_wait_p_sequence__1__2_3);
property READY__pairing__READY_wait_p_sequence__1__2_3;
 READY_wait_p_sequence
|->
 ##1 RefinementVector[2]
 && !RefinementVector[3];
endproperty

READY__pairing__READY_wait_p_sequence__2__2_3_a: assert property (disable iff(rst) READY__pairing__READY_wait_p_sequence__2__2_3);
property READY__pairing__READY_wait_p_sequence__2__2_3;
 READY_wait_p_sequence
|->
 ##1 !RefinementVector[2]
 && RefinementVector[3];
endproperty

READY__pairing__READY_wait_p_sequence__3__2_3_a: assert property (disable iff(rst) READY__pairing__READY_wait_p_sequence__3__2_3);
property READY__pairing__READY_wait_p_sequence__3__2_3;
 READY_wait_p_sequence
|->
 ##1 RefinementVector[2]
 && RefinementVector[3];
endproperty

//READY_wait_p_sequence
//pair: {3,4}
READY__pairing__READY_wait_p_sequence__0__3_4_a: assert property (disable iff(rst) READY__pairing__READY_wait_p_sequence__0__3_4);
property READY__pairing__READY_wait_p_sequence__0__3_4;
 READY_wait_p_sequence
|->
 ##1 !RefinementVector[3]
 && !RefinementVector[4];
endproperty

READY__pairing__READY_wait_p_sequence__1__3_4_a: assert property (disable iff(rst) READY__pairing__READY_wait_p_sequence__1__3_4);
property READY__pairing__READY_wait_p_sequence__1__3_4;
 READY_wait_p_sequence
|->
 ##1 RefinementVector[3]
 && !RefinementVector[4];
endproperty

READY__pairing__READY_wait_p_sequence__2__3_4_a: assert property (disable iff(rst) READY__pairing__READY_wait_p_sequence__2__3_4);
property READY__pairing__READY_wait_p_sequence__2__3_4;
 READY_wait_p_sequence
|->
 ##1 !RefinementVector[3]
 && RefinementVector[4];
endproperty

READY__pairing__READY_wait_p_sequence__3__3_4_a: assert property (disable iff(rst) READY__pairing__READY_wait_p_sequence__3__3_4);
property READY__pairing__READY_wait_p_sequence__3__3_4;
 READY_wait_p_sequence
|->
 ##1 RefinementVector[3]
 && RefinementVector[4];
endproperty

//READY_wait_p_sequence
//pair: {4,5}
READY__pairing__READY_wait_p_sequence__0__4_5_a: assert property (disable iff(rst) READY__pairing__READY_wait_p_sequence__0__4_5);
property READY__pairing__READY_wait_p_sequence__0__4_5;
 READY_wait_p_sequence
|->
 ##1 !RefinementVector[4]
 && !RefinementVector[5];
endproperty

READY__pairing__READY_wait_p_sequence__1__4_5_a: assert property (disable iff(rst) READY__pairing__READY_wait_p_sequence__1__4_5);
property READY__pairing__READY_wait_p_sequence__1__4_5;
 READY_wait_p_sequence
|->
 ##1 RefinementVector[4]
 && !RefinementVector[5];
endproperty

READY__pairing__READY_wait_p_sequence__2__4_5_a: assert property (disable iff(rst) READY__pairing__READY_wait_p_sequence__2__4_5);
property READY__pairing__READY_wait_p_sequence__2__4_5;
 READY_wait_p_sequence
|->
 ##1 !RefinementVector[4]
 && RefinementVector[5];
endproperty

READY__pairing__READY_wait_p_sequence__3__4_5_a: assert property (disable iff(rst) READY__pairing__READY_wait_p_sequence__3__4_5);
property READY__pairing__READY_wait_p_sequence__3__4_5;
 READY_wait_p_sequence
|->
 ##1 RefinementVector[4]
 && RefinementVector[5];
endproperty

//READY_wait_p_sequence
//pair: {5,6}
READY__pairing__READY_wait_p_sequence__0__5_6_a: assert property (disable iff(rst) READY__pairing__READY_wait_p_sequence__0__5_6);
property READY__pairing__READY_wait_p_sequence__0__5_6;
 READY_wait_p_sequence
|->
 ##1 !RefinementVector[5]
 && !RefinementVector[6];
endproperty

READY__pairing__READY_wait_p_sequence__1__5_6_a: assert property (disable iff(rst) READY__pairing__READY_wait_p_sequence__1__5_6);
property READY__pairing__READY_wait_p_sequence__1__5_6;
 READY_wait_p_sequence
|->
 ##1 RefinementVector[5]
 && !RefinementVector[6];
endproperty

READY__pairing__READY_wait_p_sequence__2__5_6_a: assert property (disable iff(rst) READY__pairing__READY_wait_p_sequence__2__5_6);
property READY__pairing__READY_wait_p_sequence__2__5_6;
 READY_wait_p_sequence
|->
 ##1 !RefinementVector[5]
 && RefinementVector[6];
endproperty

READY__pairing__READY_wait_p_sequence__3__5_6_a: assert property (disable iff(rst) READY__pairing__READY_wait_p_sequence__3__5_6);
property READY__pairing__READY_wait_p_sequence__3__5_6;
 READY_wait_p_sequence
|->
 ##1 RefinementVector[5]
 && RefinementVector[6];
endproperty

//READY_wait_p_sequence
//pair: {6,10}
READY__pairing__READY_wait_p_sequence__0__6_10_a: assert property (disable iff(rst) READY__pairing__READY_wait_p_sequence__0__6_10);
property READY__pairing__READY_wait_p_sequence__0__6_10;
 READY_wait_p_sequence
|->
 ##1 !RefinementVector[6]
 && !RefinementVector[10];
endproperty

READY__pairing__READY_wait_p_sequence__1__6_10_a: assert property (disable iff(rst) READY__pairing__READY_wait_p_sequence__1__6_10);
property READY__pairing__READY_wait_p_sequence__1__6_10;
 READY_wait_p_sequence
|->
 ##1 RefinementVector[6]
 && !RefinementVector[10];
endproperty

READY__pairing__READY_wait_p_sequence__2__6_10_a: assert property (disable iff(rst) READY__pairing__READY_wait_p_sequence__2__6_10);
property READY__pairing__READY_wait_p_sequence__2__6_10;
 READY_wait_p_sequence
|->
 ##1 !RefinementVector[6]
 && RefinementVector[10];
endproperty

READY__pairing__READY_wait_p_sequence__3__6_10_a: assert property (disable iff(rst) READY__pairing__READY_wait_p_sequence__3__6_10);
property READY__pairing__READY_wait_p_sequence__3__6_10;
 READY_wait_p_sequence
|->
 ##1 RefinementVector[6]
 && RefinementVector[10];
endproperty


//reset_p_sequence
//pair: {0,10}
READY__pairing__reset_p_sequence__0__0_10_a: assert property (READY__pairing__reset_p_sequence__0__0_10);
property READY__pairing__reset_p_sequence__0__0_10;
 reset_p_sequence
|->
 !RefinementVector[0]
 && !RefinementVector[10];
endproperty

READY__pairing__reset_p_sequence__1__0_10_a: assert property (READY__pairing__reset_p_sequence__1__0_10);
property READY__pairing__reset_p_sequence__1__0_10;
 reset_p_sequence
|->
 RefinementVector[0]
 && !RefinementVector[10];
endproperty

READY__pairing__reset_p_sequence__2__0_10_a: assert property (READY__pairing__reset_p_sequence__2__0_10);
property READY__pairing__reset_p_sequence__2__0_10;
 reset_p_sequence
|->
 !RefinementVector[0]
 && RefinementVector[10];
endproperty

READY__pairing__reset_p_sequence__3__0_10_a: assert property (READY__pairing__reset_p_sequence__3__0_10);
property READY__pairing__reset_p_sequence__3__0_10;
 reset_p_sequence
|->
 RefinementVector[0]
 && RefinementVector[10];
endproperty


/*********************************************/
/* STARTPARSING state bit-pairing properties */
/*********************************************/

//READY_to_STARTPARSING_p_sequence
//pair: {0,10}
STARTPARSING__pairing__READY_to_STARTPARSING_p_sequence__0__0_10_a: assert property (disable iff(rst) STARTPARSING__pairing__READY_to_STARTPARSING_p_sequence__0__0_10);
property STARTPARSING__pairing__READY_to_STARTPARSING_p_sequence__0__0_10;
 READY_to_STARTPARSING_p_sequence
|->
 ##1 !RefinementVector[0]
 && !RefinementVector[10];
endproperty

STARTPARSING__pairing__READY_to_STARTPARSING_p_sequence__1__0_10_a: assert property (disable iff(rst) STARTPARSING__pairing__READY_to_STARTPARSING_p_sequence__1__0_10);
property STARTPARSING__pairing__READY_to_STARTPARSING_p_sequence__1__0_10;
 READY_to_STARTPARSING_p_sequence
|->
 ##1 RefinementVector[0]
 && !RefinementVector[10];
endproperty

STARTPARSING__pairing__READY_to_STARTPARSING_p_sequence__2__0_10_a: assert property (disable iff(rst) STARTPARSING__pairing__READY_to_STARTPARSING_p_sequence__2__0_10);
property STARTPARSING__pairing__READY_to_STARTPARSING_p_sequence__2__0_10;
 READY_to_STARTPARSING_p_sequence
|->
 ##1 !RefinementVector[0]
 && RefinementVector[10];
endproperty

STARTPARSING__pairing__READY_to_STARTPARSING_p_sequence__3__0_10_a: assert property (disable iff(rst) STARTPARSING__pairing__READY_to_STARTPARSING_p_sequence__3__0_10);
property STARTPARSING__pairing__READY_to_STARTPARSING_p_sequence__3__0_10;
 READY_to_STARTPARSING_p_sequence
|->
 ##1 RefinementVector[0]
 && RefinementVector[10];
endproperty


//STARTPARSING_to_STARTPARSING_p_sequence
//pair: {0,1}
STARTPARSING__pairing__STARTPARSING_to_STARTPARSING_p_sequence__0__0_1_a: assert property (disable iff(rst) STARTPARSING__pairing__STARTPARSING_to_STARTPARSING_p_sequence__0__0_1);
property STARTPARSING__pairing__STARTPARSING_to_STARTPARSING_p_sequence__0__0_1;
 STARTPARSING_to_STARTPARSING_p_sequence
|->
 ##1 !RefinementVector[0]
 && !RefinementVector[1];
endproperty

STARTPARSING__pairing__STARTPARSING_to_STARTPARSING_p_sequence__1__0_1_a: assert property (disable iff(rst) STARTPARSING__pairing__STARTPARSING_to_STARTPARSING_p_sequence__1__0_1);
property STARTPARSING__pairing__STARTPARSING_to_STARTPARSING_p_sequence__1__0_1;
 STARTPARSING_to_STARTPARSING_p_sequence
|->
 ##1 RefinementVector[0]
 && !RefinementVector[1];
endproperty

STARTPARSING__pairing__STARTPARSING_to_STARTPARSING_p_sequence__2__0_1_a: assert property (disable iff(rst) STARTPARSING__pairing__STARTPARSING_to_STARTPARSING_p_sequence__2__0_1);
property STARTPARSING__pairing__STARTPARSING_to_STARTPARSING_p_sequence__2__0_1;
 STARTPARSING_to_STARTPARSING_p_sequence
|->
 ##1 !RefinementVector[0]
 && RefinementVector[1];
endproperty

STARTPARSING__pairing__STARTPARSING_to_STARTPARSING_p_sequence__3__0_1_a: assert property (disable iff(rst) STARTPARSING__pairing__STARTPARSING_to_STARTPARSING_p_sequence__3__0_1);
property STARTPARSING__pairing__STARTPARSING_to_STARTPARSING_p_sequence__3__0_1;
 STARTPARSING_to_STARTPARSING_p_sequence
|->
 ##1 RefinementVector[0]
 && RefinementVector[1];
endproperty

//STARTPARSING_to_STARTPARSING_p_sequence
//pair: {1,10}
STARTPARSING__pairing__STARTPARSING_to_STARTPARSING_p_sequence__0__1_10_a: assert property (disable iff(rst) STARTPARSING__pairing__STARTPARSING_to_STARTPARSING_p_sequence__0__1_10);
property STARTPARSING__pairing__STARTPARSING_to_STARTPARSING_p_sequence__0__1_10;
 STARTPARSING_to_STARTPARSING_p_sequence
|->
 ##1 !RefinementVector[1]
 && !RefinementVector[10];
endproperty

STARTPARSING__pairing__STARTPARSING_to_STARTPARSING_p_sequence__1__1_10_a: assert property (disable iff(rst) STARTPARSING__pairing__STARTPARSING_to_STARTPARSING_p_sequence__1__1_10);
property STARTPARSING__pairing__STARTPARSING_to_STARTPARSING_p_sequence__1__1_10;
 STARTPARSING_to_STARTPARSING_p_sequence
|->
 ##1 RefinementVector[1]
 && !RefinementVector[10];
endproperty

STARTPARSING__pairing__STARTPARSING_to_STARTPARSING_p_sequence__2__1_10_a: assert property (disable iff(rst) STARTPARSING__pairing__STARTPARSING_to_STARTPARSING_p_sequence__2__1_10);
property STARTPARSING__pairing__STARTPARSING_to_STARTPARSING_p_sequence__2__1_10;
 STARTPARSING_to_STARTPARSING_p_sequence
|->
 ##1 !RefinementVector[1]
 && RefinementVector[10];
endproperty

STARTPARSING__pairing__STARTPARSING_to_STARTPARSING_p_sequence__3__1_10_a: assert property (disable iff(rst) STARTPARSING__pairing__STARTPARSING_to_STARTPARSING_p_sequence__3__1_10);
property STARTPARSING__pairing__STARTPARSING_to_STARTPARSING_p_sequence__3__1_10;
 STARTPARSING_to_STARTPARSING_p_sequence
|->
 ##1 RefinementVector[1]
 && RefinementVector[10];
endproperty



endmodule