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
  input bit unsigned [31:0] fieldIn [N-1:0],
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

sequence s_DATAPARSING_to_s_DATAPARSING_p_sequence;
  (OptionsParser.OptionsParser_control_inst.current_state==3) &&
  (!(OptionsParser.OptionsParser_computational_inst.parsed.hasError || OptionsParser.OptionsParser_computational_inst.parsed.hasData) && ((OptionsParser.OptionsParser_computational_inst.counter < 4'd13) || (((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) == 0))) &&
  (OptionsParser.OptionsParser_computational_inst.CurrentState == DATAPARSING);
endsequence

sequence s_DATAPARSING_to_s_DATAPARSING_1_p_sequence;
  (OptionsParser.OptionsParser_control_inst.current_state==3) &&
  ((OptionsParser.OptionsParser_computational_inst.parsed.hasError || OptionsParser.OptionsParser_computational_inst.parsed.hasData) || !((OptionsParser.OptionsParser_computational_inst.counter < 4'd13) || (((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) == 0))) &&
  !((OptionsParser.OptionsParser_computational_inst.parsed.hasError || (OptionsParser.OptionsParser_computational_inst.counter > 4'd14)) || ((OptionsParser.OptionsParser_computational_inst.parsed.dataOptionLen.contents > 5) && ((OptionsParser.OptionsParser_computational_inst.parsed.dataOptionLen.position + OptionsParser.OptionsParser_computational_inst.parsed.dataOptionLen.contents) > 13))) &&
  OptionsParser.OptionsParser_computational_inst.parsed.hasData &&
  (OptionsParser.OptionsParser_computational_inst.counter <= (OptionsParser.OptionsParser_computational_inst.parsed.dataOptionLen.position + OptionsParser.OptionsParser_computational_inst.parsed.dataOptionLen.contents));
endsequence

sequence s_DATAPARSING_to_s_DATAPARSING_2_p_sequence;
  (OptionsParser.OptionsParser_control_inst.current_state==3) &&
  ((OptionsParser.OptionsParser_computational_inst.parsed.hasError || OptionsParser.OptionsParser_computational_inst.parsed.hasData) || !((OptionsParser.OptionsParser_computational_inst.counter < 4'd13) || (((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) == 0))) &&
  !((OptionsParser.OptionsParser_computational_inst.parsed.hasError || (OptionsParser.OptionsParser_computational_inst.counter > 4'd14)) || ((OptionsParser.OptionsParser_computational_inst.parsed.dataOptionLen.contents > 5) && ((OptionsParser.OptionsParser_computational_inst.parsed.dataOptionLen.position + OptionsParser.OptionsParser_computational_inst.parsed.dataOptionLen.contents) > 13))) &&
  !(OptionsParser.OptionsParser_computational_inst.parsed.hasData && (OptionsParser.OptionsParser_computational_inst.counter <= (OptionsParser.OptionsParser_computational_inst.parsed.dataOptionLen.position + OptionsParser.OptionsParser_computational_inst.parsed.dataOptionLen.contents))) &&
  (((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) != 2) &&
  ((((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) != 3) || OptionsParser.OptionsParser_computational_inst.parsed.hasInfo) &&
  (OptionsParser.OptionsParser_computational_inst.CurrentState == DATAPARSING);
endsequence

sequence s_DATAPARSING_to_s_DONE_p_sequence;
  (OptionsParser.OptionsParser_control_inst.current_state==3) &&
  ((OptionsParser.OptionsParser_computational_inst.parsed.hasError || OptionsParser.OptionsParser_computational_inst.parsed.hasData) || !((OptionsParser.OptionsParser_computational_inst.counter < 4'd13) || (((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) == 0))) &&
  ((OptionsParser.OptionsParser_computational_inst.parsed.hasError || (OptionsParser.OptionsParser_computational_inst.counter > 4'd14)) || ((OptionsParser.OptionsParser_computational_inst.parsed.dataOptionLen.contents > 5) && ((OptionsParser.OptionsParser_computational_inst.parsed.dataOptionLen.position + OptionsParser.OptionsParser_computational_inst.parsed.dataOptionLen.contents) > 13)));
endsequence

sequence s_DATAPARSING_to_s_ENDPARSING_p_sequence;
  (OptionsParser.OptionsParser_control_inst.current_state==3) &&
  ((OptionsParser.OptionsParser_computational_inst.parsed.hasError || OptionsParser.OptionsParser_computational_inst.parsed.hasData) || !((OptionsParser.OptionsParser_computational_inst.counter < 4'd13) || (((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) == 0))) &&
  !((OptionsParser.OptionsParser_computational_inst.parsed.hasError || (OptionsParser.OptionsParser_computational_inst.counter > 4'd14)) || ((OptionsParser.OptionsParser_computational_inst.parsed.dataOptionLen.contents > 5) && ((OptionsParser.OptionsParser_computational_inst.parsed.dataOptionLen.position + OptionsParser.OptionsParser_computational_inst.parsed.dataOptionLen.contents) > 13))) &&
  !(OptionsParser.OptionsParser_computational_inst.parsed.hasData && (OptionsParser.OptionsParser_computational_inst.counter <= (OptionsParser.OptionsParser_computational_inst.parsed.dataOptionLen.position + OptionsParser.OptionsParser_computational_inst.parsed.dataOptionLen.contents))) &&
  (((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) == 2);
endsequence

sequence s_DATAPARSING_to_s_INFOPARSING_p_sequence;
  (OptionsParser.OptionsParser_control_inst.current_state==3) &&
  ((OptionsParser.OptionsParser_computational_inst.parsed.hasError || OptionsParser.OptionsParser_computational_inst.parsed.hasData) || !((OptionsParser.OptionsParser_computational_inst.counter < 4'd13) || (((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) == 0))) &&
  !((OptionsParser.OptionsParser_computational_inst.parsed.hasError || (OptionsParser.OptionsParser_computational_inst.counter > 4'd14)) || ((OptionsParser.OptionsParser_computational_inst.parsed.dataOptionLen.contents > 5) && ((OptionsParser.OptionsParser_computational_inst.parsed.dataOptionLen.position + OptionsParser.OptionsParser_computational_inst.parsed.dataOptionLen.contents) > 13))) &&
  !(OptionsParser.OptionsParser_computational_inst.parsed.hasData && (OptionsParser.OptionsParser_computational_inst.counter <= (OptionsParser.OptionsParser_computational_inst.parsed.dataOptionLen.position + OptionsParser.OptionsParser_computational_inst.parsed.dataOptionLen.contents))) &&
  (((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) != 2) &&
  ((((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) == 3) && !OptionsParser.OptionsParser_computational_inst.parsed.hasInfo);
endsequence

sequence s_DONE_to_s_READY_p_sequence;
  (OptionsParser.OptionsParser_control_inst.current_state==5) &&
  OptionsParser.parsedOut_sync;
endsequence

sequence s_ENDPARSING_to_s_DONE_p_sequence;
  (OptionsParser.OptionsParser_control_inst.current_state==4);
endsequence

sequence s_INFOPARSING_to_s_DATAPARSING_p_sequence;
  (OptionsParser.OptionsParser_control_inst.current_state==2) &&
  (OptionsParser.OptionsParser_computational_inst.parsed.hasInfo || (OptionsParser.OptionsParser_computational_inst.counter >= 4'd13)) &&
  (OptionsParser.OptionsParser_computational_inst.counter <= 4'd14) &&
  (((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) != 2) &&
  (((((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) == 4) && !OptionsParser.OptionsParser_computational_inst.parsed.hasData) && (OptionsParser.OptionsParser_computational_inst.counter < 12)) &&
  (((((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) > 5) || ((((((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) + OptionsParser.OptionsParser_computational_inst.counter) + 1) > 13));
endsequence

sequence s_INFOPARSING_to_s_DATAPARSING_1_p_sequence;
  (OptionsParser.OptionsParser_control_inst.current_state==2) &&
  (OptionsParser.OptionsParser_computational_inst.parsed.hasInfo || (OptionsParser.OptionsParser_computational_inst.counter >= 4'd13)) &&
  (OptionsParser.OptionsParser_computational_inst.counter <= 4'd14) &&
  (((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) != 2) &&
  (((((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) == 4) && !OptionsParser.OptionsParser_computational_inst.parsed.hasData) && (OptionsParser.OptionsParser_computational_inst.counter < 12)) &&
  !(((((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) > 5) || ((((((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) + OptionsParser.OptionsParser_computational_inst.counter) + 1) > 13));
endsequence

sequence s_INFOPARSING_to_s_DONE_p_sequence;
  (OptionsParser.OptionsParser_control_inst.current_state==2) &&
  (OptionsParser.OptionsParser_computational_inst.parsed.hasInfo || (OptionsParser.OptionsParser_computational_inst.counter >= 4'd13)) &&
  (OptionsParser.OptionsParser_computational_inst.counter > 4'd14);
endsequence

sequence s_INFOPARSING_to_s_ENDPARSING_p_sequence;
  (OptionsParser.OptionsParser_control_inst.current_state==2) &&
  (OptionsParser.OptionsParser_computational_inst.parsed.hasInfo || (OptionsParser.OptionsParser_computational_inst.counter >= 4'd13)) &&
  (OptionsParser.OptionsParser_computational_inst.counter <= 4'd14) &&
  (((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) == 2);
endsequence

sequence s_INFOPARSING_to_s_INFOPARSING_p_sequence;
  (OptionsParser.OptionsParser_control_inst.current_state==2) &&
  !OptionsParser.OptionsParser_computational_inst.parsed.hasInfo &&
  (OptionsParser.OptionsParser_computational_inst.counter < 4'd13) &&
  (OptionsParser.OptionsParser_computational_inst.CurrentState == INFOPARSING);
endsequence

sequence s_INFOPARSING_to_s_INFOPARSING_1_p_sequence;
  (OptionsParser.OptionsParser_control_inst.current_state==2) &&
  (OptionsParser.OptionsParser_computational_inst.parsed.hasInfo || (OptionsParser.OptionsParser_computational_inst.counter >= 4'd13)) &&
  (OptionsParser.OptionsParser_computational_inst.counter <= 4'd14) &&
  (((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) != 2) &&
  !(((((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) == 4) && !OptionsParser.OptionsParser_computational_inst.parsed.hasData) && (OptionsParser.OptionsParser_computational_inst.counter < 12));
endsequence

sequence s_READY_to_s_STARTPARSING_p_sequence;
  (OptionsParser.OptionsParser_control_inst.current_state==0) &&
  OptionsParser.fieldsIn_sync;
endsequence

sequence s_STARTPARSING_to_s_DATAPARSING_p_sequence;
  (OptionsParser.OptionsParser_control_inst.current_state==1) &&
  (OptionsParser.OptionsParser_computational_inst.counter <= 4'd14) &&
  !((((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) == 2) && OptionsParser.OptionsParser_computational_inst.parsed.hasStart) &&
  !((((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) == 3) && OptionsParser.OptionsParser_computational_inst.parsed.hasStart) &&
  (((((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) == 4) && OptionsParser.OptionsParser_computational_inst.parsed.hasStart) && (OptionsParser.OptionsParser_computational_inst.counter < 12)) &&
  (((((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) > 5) || ((((((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) + OptionsParser.OptionsParser_computational_inst.counter) + 1) > 13));
endsequence

sequence s_STARTPARSING_to_s_DATAPARSING_1_p_sequence;
  (OptionsParser.OptionsParser_control_inst.current_state==1) &&
  (OptionsParser.OptionsParser_computational_inst.counter <= 4'd14) &&
  !((((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) == 2) && OptionsParser.OptionsParser_computational_inst.parsed.hasStart) &&
  !((((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) == 3) && OptionsParser.OptionsParser_computational_inst.parsed.hasStart) &&
  (((((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) == 4) && OptionsParser.OptionsParser_computational_inst.parsed.hasStart) && (OptionsParser.OptionsParser_computational_inst.counter < 12)) &&
  !(((((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) > 5) || ((((((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : (((OptionsParser.OptionsParser_computational_inst.counter + 4'd1) == 5'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) + OptionsParser.OptionsParser_computational_inst.counter) + 1) > 13));
endsequence

sequence s_STARTPARSING_to_s_DONE_p_sequence;
  (OptionsParser.OptionsParser_control_inst.current_state==1) &&
  (OptionsParser.OptionsParser_computational_inst.counter > 4'd14);
endsequence

sequence s_STARTPARSING_to_s_ENDPARSING_p_sequence;
  (OptionsParser.OptionsParser_control_inst.current_state==1) &&
  (OptionsParser.OptionsParser_computational_inst.counter <= 4'd14) &&
  ((((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) == 2) && OptionsParser.OptionsParser_computational_inst.parsed.hasStart);
endsequence

sequence s_STARTPARSING_to_s_INFOPARSING_p_sequence;
  (OptionsParser.OptionsParser_control_inst.current_state==1) &&
  (OptionsParser.OptionsParser_computational_inst.counter <= 4'd14) &&
  !((((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) == 2) && OptionsParser.OptionsParser_computational_inst.parsed.hasStart) &&
  ((((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) == 3) && OptionsParser.OptionsParser_computational_inst.parsed.hasStart);
endsequence

sequence s_STARTPARSING_to_s_STARTPARSING_p_sequence;
  (OptionsParser.OptionsParser_control_inst.current_state==1) &&
  (OptionsParser.OptionsParser_computational_inst.counter <= 4'd14) &&
  !((((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) == 2) && (((((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) == 1) && (OptionsParser.OptionsParser_computational_inst.counter < 4'd15)) ? 1 : OptionsParser.OptionsParser_computational_inst.parsed.hasStart)) &&
  !((((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) == 3) && (((((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) == 1) && (OptionsParser.OptionsParser_computational_inst.counter < 4'd15)) ? 1 : OptionsParser.OptionsParser_computational_inst.parsed.hasStart)) &&
  !(((((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) == 4) && (((((OptionsParser.OptionsParser_computational_inst.counter == 4'd0) ? OptionsParser.OptionsParser_computational_inst.fields [0] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd1) ? OptionsParser.OptionsParser_computational_inst.fields [1] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd2) ? OptionsParser.OptionsParser_computational_inst.fields [2] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd3) ? OptionsParser.OptionsParser_computational_inst.fields [3] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd4) ? OptionsParser.OptionsParser_computational_inst.fields [4] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd5) ? OptionsParser.OptionsParser_computational_inst.fields [5] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd6) ? OptionsParser.OptionsParser_computational_inst.fields [6] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd7) ? OptionsParser.OptionsParser_computational_inst.fields [7] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd8) ? OptionsParser.OptionsParser_computational_inst.fields [8] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd9) ? OptionsParser.OptionsParser_computational_inst.fields [9] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd10) ? OptionsParser.OptionsParser_computational_inst.fields [10] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd11) ? OptionsParser.OptionsParser_computational_inst.fields [11] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd12) ? OptionsParser.OptionsParser_computational_inst.fields [12] : ((OptionsParser.OptionsParser_computational_inst.counter == 4'd13) ? OptionsParser.OptionsParser_computational_inst.fields [13] : OptionsParser.OptionsParser_computational_inst.fields [14])))))))))))))) == 1) && (OptionsParser.OptionsParser_computational_inst.counter < 4'd15)) ? 1 : OptionsParser.OptionsParser_computational_inst.parsed.hasStart)) && (OptionsParser.OptionsParser_computational_inst.counter < 12));
endsequence

sequence s_DONE_wait_p_sequence;
  (OptionsParser.OptionsParser_control_inst.current_state==5) &&
  !OptionsParser.parsedOut_sync;
endsequence

sequence s_READY_wait_p_sequence;
  (OptionsParser.OptionsParser_control_inst.current_state==0) &&
  !OptionsParser.fieldsIn_sync;
endsequence

reset_a_fieldsIn_notify_ec: assert property (reset_p_fieldsIn_notify_ec);
property reset_p_fieldsIn_notify_ec;
  bit fieldsIn_notify_store; //Store the value of the output from the generated RTL
  reset_p_sequence
  ##0 (1'b1, fieldsIn_notify_store = OptionsParser.fieldsIn_notify)
  |->
  ##[0:15] fieldsIn_notify_store == ready;
endproperty

reset_a_parsedOut_notify_ec: assert property (reset_p_parsedOut_notify_ec);
property reset_p_parsedOut_notify_ec;
  bit parsedOut_notify_store; //Store the value of the output from the generated RTL
  reset_p_sequence
  ##0 (1'b1, parsedOut_notify_store = OptionsParser.parsedOut_notify)
  |->
  ##[0:15] parsedOut_notify_store == done;
endproperty

//Internal transition assertion, checks hsk signals
s_DATAPARSING_to_s_DATAPARSING_a_ec: assert property (disable iff(rst) s_DATAPARSING_to_s_DATAPARSING_p_ec);
property s_DATAPARSING_to_s_DATAPARSING_p_ec;
  s_DATAPARSING_to_s_DATAPARSING_p_sequence
  |->
  ##1 (ready == 0) and
  ##1 (done == 0);
endproperty

//Internal transition assertion, checks hsk signals
s_DATAPARSING_to_s_DATAPARSING_1_a_ec: assert property (disable iff(rst) s_DATAPARSING_to_s_DATAPARSING_1_p_ec);
property s_DATAPARSING_to_s_DATAPARSING_1_p_ec;
  s_DATAPARSING_to_s_DATAPARSING_1_p_sequence
  |->
  ##1 (ready == 0) and
  ##1 (done == 0);
endproperty

//Internal transition assertion, checks hsk signals
s_DATAPARSING_to_s_DATAPARSING_2_a_ec: assert property (disable iff(rst) s_DATAPARSING_to_s_DATAPARSING_2_p_ec);
property s_DATAPARSING_to_s_DATAPARSING_2_p_ec;
  s_DATAPARSING_to_s_DATAPARSING_2_p_sequence
  |->
  ##1 (ready == 0) and
  ##1 (done == 0);
endproperty

s_DATAPARSING_to_s_DONE_a_fieldsIn_notify_ec: assert property (disable iff(rst) s_DATAPARSING_to_s_DONE_p_fieldsIn_notify_ec);
property s_DATAPARSING_to_s_DONE_p_fieldsIn_notify_ec;
  bit fieldsIn_notify_store; //Store the value of the output from the generated RTL
  s_DATAPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, fieldsIn_notify_store = OptionsParser.fieldsIn_notify)
  |->
  ##[0:15] fieldsIn_notify_store == ready;
endproperty

s_DATAPARSING_to_s_DONE_a_parsedOut_sig_hasStart_ec: assert property (disable iff(rst) s_DATAPARSING_to_s_DONE_p_parsedOut_sig_hasStart_ec);
property s_DATAPARSING_to_s_DONE_p_parsedOut_sig_hasStart_ec;
  bit parsedOut_sig_hasStart_store; //Store the value of the output from the generated RTL
  s_DATAPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_hasStart_store = OptionsParser.parsedOut_sig.hasStart)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_hasStart_store == parsed.hasStart;
endproperty

s_DATAPARSING_to_s_DONE_a_parsedOut_sig_hasInfo_ec: assert property (disable iff(rst) s_DATAPARSING_to_s_DONE_p_parsedOut_sig_hasInfo_ec);
property s_DATAPARSING_to_s_DONE_p_parsedOut_sig_hasInfo_ec;
  bit parsedOut_sig_hasInfo_store; //Store the value of the output from the generated RTL
  s_DATAPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_hasInfo_store = OptionsParser.parsedOut_sig.hasInfo)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_hasInfo_store == parsed.hasInfo;
endproperty

s_DATAPARSING_to_s_DONE_a_parsedOut_sig_hasData_ec: assert property (disable iff(rst) s_DATAPARSING_to_s_DONE_p_parsedOut_sig_hasData_ec);
property s_DATAPARSING_to_s_DONE_p_parsedOut_sig_hasData_ec;
  bit parsedOut_sig_hasData_store; //Store the value of the output from the generated RTL
  s_DATAPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_hasData_store = OptionsParser.parsedOut_sig.hasData)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_hasData_store == parsed.hasData;
endproperty

s_DATAPARSING_to_s_DONE_a_parsedOut_sig_hasEnd_ec: assert property (disable iff(rst) s_DATAPARSING_to_s_DONE_p_parsedOut_sig_hasEnd_ec);
property s_DATAPARSING_to_s_DONE_p_parsedOut_sig_hasEnd_ec;
  bit parsedOut_sig_hasEnd_store; //Store the value of the output from the generated RTL
  s_DATAPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_hasEnd_store = OptionsParser.parsedOut_sig.hasEnd)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_hasEnd_store == parsed.hasEnd;
endproperty

s_DATAPARSING_to_s_DONE_a_parsedOut_sig_isEmpty_ec: assert property (disable iff(rst) s_DATAPARSING_to_s_DONE_p_parsedOut_sig_isEmpty_ec);
property s_DATAPARSING_to_s_DONE_p_parsedOut_sig_isEmpty_ec;
  bit parsedOut_sig_isEmpty_store; //Store the value of the output from the generated RTL
  s_DATAPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_isEmpty_store = OptionsParser.parsedOut_sig.isEmpty)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_isEmpty_store == parsed.isEmpty;
endproperty

s_DATAPARSING_to_s_DONE_a_parsedOut_sig_hasError_ec: assert property (disable iff(rst) s_DATAPARSING_to_s_DONE_p_parsedOut_sig_hasError_ec);
property s_DATAPARSING_to_s_DONE_p_parsedOut_sig_hasError_ec;
  bit parsedOut_sig_hasError_store; //Store the value of the output from the generated RTL
  s_DATAPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_hasError_store = OptionsParser.parsedOut_sig.hasError)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_hasError_store == parsed.hasError;
endproperty

s_DATAPARSING_to_s_DONE_a_parsedOut_sig_startOption_position_ec: assert property (disable iff(rst) s_DATAPARSING_to_s_DONE_p_parsedOut_sig_startOption_position_ec);
property s_DATAPARSING_to_s_DONE_p_parsedOut_sig_startOption_position_ec;
  bit unsigned [31:0] parsedOut_sig_startOption_position_store; //Store the value of the output from the generated RTL
  s_DATAPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_startOption_position_store = OptionsParser.parsedOut_sig.startOption.position)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_startOption_position_store == parsed.startOption.position;
endproperty

s_DATAPARSING_to_s_DONE_a_parsedOut_sig_startOption_contents_ec: assert property (disable iff(rst) s_DATAPARSING_to_s_DONE_p_parsedOut_sig_startOption_contents_ec);
property s_DATAPARSING_to_s_DONE_p_parsedOut_sig_startOption_contents_ec;
  bit unsigned [31:0] parsedOut_sig_startOption_contents_store; //Store the value of the output from the generated RTL
  s_DATAPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_startOption_contents_store = OptionsParser.parsedOut_sig.startOption.contents)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_startOption_contents_store == parsed.startOption.contents;
endproperty

s_DATAPARSING_to_s_DONE_a_parsedOut_sig_startOption_optiontype_ec: assert property (disable iff(rst) s_DATAPARSING_to_s_DONE_p_parsedOut_sig_startOption_optiontype_ec);
property s_DATAPARSING_to_s_DONE_p_parsedOut_sig_startOption_optiontype_ec;
  e_options parsedOut_sig_startOption_optiontype_store; //Store the value of the output from the generated RTL
  s_DATAPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_startOption_optiontype_store = OptionsParser.parsedOut_sig.startOption.optiontype)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_startOption_optiontype_store == parsed.startOption.OptionType;
endproperty

s_DATAPARSING_to_s_DONE_a_parsedOut_sig_endOption_position_ec: assert property (disable iff(rst) s_DATAPARSING_to_s_DONE_p_parsedOut_sig_endOption_position_ec);
property s_DATAPARSING_to_s_DONE_p_parsedOut_sig_endOption_position_ec;
  bit unsigned [31:0] parsedOut_sig_endOption_position_store; //Store the value of the output from the generated RTL
  s_DATAPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_endOption_position_store = OptionsParser.parsedOut_sig.endOption.position)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_endOption_position_store == parsed.endOption.position;
endproperty

s_DATAPARSING_to_s_DONE_a_parsedOut_sig_endOption_contents_ec: assert property (disable iff(rst) s_DATAPARSING_to_s_DONE_p_parsedOut_sig_endOption_contents_ec);
property s_DATAPARSING_to_s_DONE_p_parsedOut_sig_endOption_contents_ec;
  bit unsigned [31:0] parsedOut_sig_endOption_contents_store; //Store the value of the output from the generated RTL
  s_DATAPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_endOption_contents_store = OptionsParser.parsedOut_sig.endOption.contents)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_endOption_contents_store == parsed.endOption.contents;
endproperty

s_DATAPARSING_to_s_DONE_a_parsedOut_sig_endOption_optiontype_ec: assert property (disable iff(rst) s_DATAPARSING_to_s_DONE_p_parsedOut_sig_endOption_optiontype_ec);
property s_DATAPARSING_to_s_DONE_p_parsedOut_sig_endOption_optiontype_ec;
  e_options parsedOut_sig_endOption_optiontype_store; //Store the value of the output from the generated RTL
  s_DATAPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_endOption_optiontype_store = OptionsParser.parsedOut_sig.endOption.optiontype)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_endOption_optiontype_store == parsed.endOption.OptionType;
endproperty

s_DATAPARSING_to_s_DONE_a_parsedOut_sig_infoOption_position_ec: assert property (disable iff(rst) s_DATAPARSING_to_s_DONE_p_parsedOut_sig_infoOption_position_ec);
property s_DATAPARSING_to_s_DONE_p_parsedOut_sig_infoOption_position_ec;
  bit unsigned [31:0] parsedOut_sig_infoOption_position_store; //Store the value of the output from the generated RTL
  s_DATAPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_infoOption_position_store = OptionsParser.parsedOut_sig.infoOption.position)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_infoOption_position_store == parsed.infoOption.position;
endproperty

s_DATAPARSING_to_s_DONE_a_parsedOut_sig_infoOption_contents_ec: assert property (disable iff(rst) s_DATAPARSING_to_s_DONE_p_parsedOut_sig_infoOption_contents_ec);
property s_DATAPARSING_to_s_DONE_p_parsedOut_sig_infoOption_contents_ec;
  bit unsigned [31:0] parsedOut_sig_infoOption_contents_store; //Store the value of the output from the generated RTL
  s_DATAPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_infoOption_contents_store = OptionsParser.parsedOut_sig.infoOption.contents)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_infoOption_contents_store == parsed.infoOption.contents;
endproperty

s_DATAPARSING_to_s_DONE_a_parsedOut_sig_infoOption_optiontype_ec: assert property (disable iff(rst) s_DATAPARSING_to_s_DONE_p_parsedOut_sig_infoOption_optiontype_ec);
property s_DATAPARSING_to_s_DONE_p_parsedOut_sig_infoOption_optiontype_ec;
  e_options parsedOut_sig_infoOption_optiontype_store; //Store the value of the output from the generated RTL
  s_DATAPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_infoOption_optiontype_store = OptionsParser.parsedOut_sig.infoOption.optiontype)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_infoOption_optiontype_store == parsed.infoOption.OptionType;
endproperty

s_DATAPARSING_to_s_DONE_a_parsedOut_sig_infoOptionContents_position_ec: assert property (disable iff(rst) s_DATAPARSING_to_s_DONE_p_parsedOut_sig_infoOptionContents_position_ec);
property s_DATAPARSING_to_s_DONE_p_parsedOut_sig_infoOptionContents_position_ec;
  bit unsigned [31:0] parsedOut_sig_infoOptionContents_position_store; //Store the value of the output from the generated RTL
  s_DATAPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_infoOptionContents_position_store = OptionsParser.parsedOut_sig.infoOptionContents.position)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_infoOptionContents_position_store == parsed.infoOptionContents.position;
endproperty

s_DATAPARSING_to_s_DONE_a_parsedOut_sig_infoOptionContents_contents_ec: assert property (disable iff(rst) s_DATAPARSING_to_s_DONE_p_parsedOut_sig_infoOptionContents_contents_ec);
property s_DATAPARSING_to_s_DONE_p_parsedOut_sig_infoOptionContents_contents_ec;
  bit unsigned [31:0] parsedOut_sig_infoOptionContents_contents_store; //Store the value of the output from the generated RTL
  s_DATAPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_infoOptionContents_contents_store = OptionsParser.parsedOut_sig.infoOptionContents.contents)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_infoOptionContents_contents_store == parsed.infoOptionContents.contents;
endproperty

s_DATAPARSING_to_s_DONE_a_parsedOut_sig_infoOptionContents_optiontype_ec: assert property (disable iff(rst) s_DATAPARSING_to_s_DONE_p_parsedOut_sig_infoOptionContents_optiontype_ec);
property s_DATAPARSING_to_s_DONE_p_parsedOut_sig_infoOptionContents_optiontype_ec;
  e_options parsedOut_sig_infoOptionContents_optiontype_store; //Store the value of the output from the generated RTL
  s_DATAPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_infoOptionContents_optiontype_store = OptionsParser.parsedOut_sig.infoOptionContents.optiontype)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_infoOptionContents_optiontype_store == parsed.infoOptionContents.OptionType;
endproperty

s_DATAPARSING_to_s_DONE_a_parsedOut_sig_dataOption_position_ec: assert property (disable iff(rst) s_DATAPARSING_to_s_DONE_p_parsedOut_sig_dataOption_position_ec);
property s_DATAPARSING_to_s_DONE_p_parsedOut_sig_dataOption_position_ec;
  bit unsigned [31:0] parsedOut_sig_dataOption_position_store; //Store the value of the output from the generated RTL
  s_DATAPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_dataOption_position_store = OptionsParser.parsedOut_sig.dataOption.position)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_dataOption_position_store == parsed.dataOption.position;
endproperty

s_DATAPARSING_to_s_DONE_a_parsedOut_sig_dataOption_contents_ec: assert property (disable iff(rst) s_DATAPARSING_to_s_DONE_p_parsedOut_sig_dataOption_contents_ec);
property s_DATAPARSING_to_s_DONE_p_parsedOut_sig_dataOption_contents_ec;
  bit unsigned [31:0] parsedOut_sig_dataOption_contents_store; //Store the value of the output from the generated RTL
  s_DATAPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_dataOption_contents_store = OptionsParser.parsedOut_sig.dataOption.contents)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_dataOption_contents_store == parsed.dataOption.contents;
endproperty

s_DATAPARSING_to_s_DONE_a_parsedOut_sig_dataOption_optiontype_ec: assert property (disable iff(rst) s_DATAPARSING_to_s_DONE_p_parsedOut_sig_dataOption_optiontype_ec);
property s_DATAPARSING_to_s_DONE_p_parsedOut_sig_dataOption_optiontype_ec;
  e_options parsedOut_sig_dataOption_optiontype_store; //Store the value of the output from the generated RTL
  s_DATAPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_dataOption_optiontype_store = OptionsParser.parsedOut_sig.dataOption.optiontype)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_dataOption_optiontype_store == parsed.dataOption.OptionType;
endproperty

s_DATAPARSING_to_s_DONE_a_parsedOut_sig_dataOptionLen_position_ec: assert property (disable iff(rst) s_DATAPARSING_to_s_DONE_p_parsedOut_sig_dataOptionLen_position_ec);
property s_DATAPARSING_to_s_DONE_p_parsedOut_sig_dataOptionLen_position_ec;
  bit unsigned [31:0] parsedOut_sig_dataOptionLen_position_store; //Store the value of the output from the generated RTL
  s_DATAPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_dataOptionLen_position_store = OptionsParser.parsedOut_sig.dataOptionLen.position)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_dataOptionLen_position_store == parsed.dataOptionLen.position;
endproperty

s_DATAPARSING_to_s_DONE_a_parsedOut_sig_dataOptionLen_contents_ec: assert property (disable iff(rst) s_DATAPARSING_to_s_DONE_p_parsedOut_sig_dataOptionLen_contents_ec);
property s_DATAPARSING_to_s_DONE_p_parsedOut_sig_dataOptionLen_contents_ec;
  bit unsigned [31:0] parsedOut_sig_dataOptionLen_contents_store; //Store the value of the output from the generated RTL
  s_DATAPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_dataOptionLen_contents_store = OptionsParser.parsedOut_sig.dataOptionLen.contents)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_dataOptionLen_contents_store == parsed.dataOptionLen.contents;
endproperty

s_DATAPARSING_to_s_DONE_a_parsedOut_sig_dataOptionLen_optiontype_ec: assert property (disable iff(rst) s_DATAPARSING_to_s_DONE_p_parsedOut_sig_dataOptionLen_optiontype_ec);
property s_DATAPARSING_to_s_DONE_p_parsedOut_sig_dataOptionLen_optiontype_ec;
  e_options parsedOut_sig_dataOptionLen_optiontype_store; //Store the value of the output from the generated RTL
  s_DATAPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_dataOptionLen_optiontype_store = OptionsParser.parsedOut_sig.dataOptionLen.optiontype)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_dataOptionLen_optiontype_store == parsed.dataOptionLen.OptionType;
endproperty

s_DATAPARSING_to_s_DONE_a_parsedOut_notify_ec: assert property (disable iff(rst) s_DATAPARSING_to_s_DONE_p_parsedOut_notify_ec);
property s_DATAPARSING_to_s_DONE_p_parsedOut_notify_ec;
  bit parsedOut_notify_store; //Store the value of the output from the generated RTL
  s_DATAPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_notify_store = OptionsParser.parsedOut_notify)
  |->
  ##[0:15] parsedOut_notify_store == done;
endproperty

//Internal transition assertion, checks hsk signals
s_DATAPARSING_to_s_ENDPARSING_a_ec: assert property (disable iff(rst) s_DATAPARSING_to_s_ENDPARSING_p_ec);
property s_DATAPARSING_to_s_ENDPARSING_p_ec;
  s_DATAPARSING_to_s_ENDPARSING_p_sequence
  |->
  ##1 (ready == 0) and
  ##1 (done == 0);
endproperty

//Internal transition assertion, checks hsk signals
s_DATAPARSING_to_s_INFOPARSING_a_ec: assert property (disable iff(rst) s_DATAPARSING_to_s_INFOPARSING_p_ec);
property s_DATAPARSING_to_s_INFOPARSING_p_ec;
  s_DATAPARSING_to_s_INFOPARSING_p_sequence
  |->
  ##1 (ready == 0) and
  ##1 (done == 0);
endproperty

s_DONE_to_s_READY_a_fieldsIn_notify_ec: assert property (disable iff(rst) s_DONE_to_s_READY_p_fieldsIn_notify_ec);
property s_DONE_to_s_READY_p_fieldsIn_notify_ec;
  bit fieldsIn_notify_store; //Store the value of the output from the generated RTL
  s_DONE_to_s_READY_p_sequence
  ##1 (1'b1, fieldsIn_notify_store = OptionsParser.fieldsIn_notify)
  |->
  ##[0:15] fieldsIn_notify_store == ready;
endproperty

s_DONE_to_s_READY_a_parsedOut_notify_ec: assert property (disable iff(rst) s_DONE_to_s_READY_p_parsedOut_notify_ec);
property s_DONE_to_s_READY_p_parsedOut_notify_ec;
  bit parsedOut_notify_store; //Store the value of the output from the generated RTL
  s_DONE_to_s_READY_p_sequence
  ##1 (1'b1, parsedOut_notify_store = OptionsParser.parsedOut_notify)
  |->
  ##[0:15] parsedOut_notify_store == done;
endproperty

s_ENDPARSING_to_s_DONE_a_fieldsIn_notify_ec: assert property (disable iff(rst) s_ENDPARSING_to_s_DONE_p_fieldsIn_notify_ec);
property s_ENDPARSING_to_s_DONE_p_fieldsIn_notify_ec;
  bit fieldsIn_notify_store; //Store the value of the output from the generated RTL
  s_ENDPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, fieldsIn_notify_store = OptionsParser.fieldsIn_notify)
  |->
  ##[0:15] fieldsIn_notify_store == ready;
endproperty

s_ENDPARSING_to_s_DONE_a_parsedOut_sig_hasStart_ec: assert property (disable iff(rst) s_ENDPARSING_to_s_DONE_p_parsedOut_sig_hasStart_ec);
property s_ENDPARSING_to_s_DONE_p_parsedOut_sig_hasStart_ec;
  bit parsedOut_sig_hasStart_store; //Store the value of the output from the generated RTL
  s_ENDPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_hasStart_store = OptionsParser.parsedOut_sig.hasStart)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_hasStart_store == parsed.hasStart;
endproperty

s_ENDPARSING_to_s_DONE_a_parsedOut_sig_hasInfo_ec: assert property (disable iff(rst) s_ENDPARSING_to_s_DONE_p_parsedOut_sig_hasInfo_ec);
property s_ENDPARSING_to_s_DONE_p_parsedOut_sig_hasInfo_ec;
  bit parsedOut_sig_hasInfo_store; //Store the value of the output from the generated RTL
  s_ENDPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_hasInfo_store = OptionsParser.parsedOut_sig.hasInfo)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_hasInfo_store == parsed.hasInfo;
endproperty

s_ENDPARSING_to_s_DONE_a_parsedOut_sig_hasData_ec: assert property (disable iff(rst) s_ENDPARSING_to_s_DONE_p_parsedOut_sig_hasData_ec);
property s_ENDPARSING_to_s_DONE_p_parsedOut_sig_hasData_ec;
  bit parsedOut_sig_hasData_store; //Store the value of the output from the generated RTL
  s_ENDPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_hasData_store = OptionsParser.parsedOut_sig.hasData)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_hasData_store == parsed.hasData;
endproperty

s_ENDPARSING_to_s_DONE_a_parsedOut_sig_hasEnd_ec: assert property (disable iff(rst) s_ENDPARSING_to_s_DONE_p_parsedOut_sig_hasEnd_ec);
property s_ENDPARSING_to_s_DONE_p_parsedOut_sig_hasEnd_ec;
  bit parsedOut_sig_hasEnd_store; //Store the value of the output from the generated RTL
  s_ENDPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_hasEnd_store = OptionsParser.parsedOut_sig.hasEnd)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_hasEnd_store == parsed.hasEnd;
endproperty

s_ENDPARSING_to_s_DONE_a_parsedOut_sig_isEmpty_ec: assert property (disable iff(rst) s_ENDPARSING_to_s_DONE_p_parsedOut_sig_isEmpty_ec);
property s_ENDPARSING_to_s_DONE_p_parsedOut_sig_isEmpty_ec;
  bit parsedOut_sig_isEmpty_store; //Store the value of the output from the generated RTL
  s_ENDPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_isEmpty_store = OptionsParser.parsedOut_sig.isEmpty)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_isEmpty_store == parsed.isEmpty;
endproperty

s_ENDPARSING_to_s_DONE_a_parsedOut_sig_hasError_ec: assert property (disable iff(rst) s_ENDPARSING_to_s_DONE_p_parsedOut_sig_hasError_ec);
property s_ENDPARSING_to_s_DONE_p_parsedOut_sig_hasError_ec;
  bit parsedOut_sig_hasError_store; //Store the value of the output from the generated RTL
  s_ENDPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_hasError_store = OptionsParser.parsedOut_sig.hasError)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_hasError_store == parsed.hasError;
endproperty

s_ENDPARSING_to_s_DONE_a_parsedOut_sig_startOption_position_ec: assert property (disable iff(rst) s_ENDPARSING_to_s_DONE_p_parsedOut_sig_startOption_position_ec);
property s_ENDPARSING_to_s_DONE_p_parsedOut_sig_startOption_position_ec;
  bit unsigned [31:0] parsedOut_sig_startOption_position_store; //Store the value of the output from the generated RTL
  s_ENDPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_startOption_position_store = OptionsParser.parsedOut_sig.startOption.position)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_startOption_position_store == parsed.startOption.position;
endproperty

s_ENDPARSING_to_s_DONE_a_parsedOut_sig_startOption_contents_ec: assert property (disable iff(rst) s_ENDPARSING_to_s_DONE_p_parsedOut_sig_startOption_contents_ec);
property s_ENDPARSING_to_s_DONE_p_parsedOut_sig_startOption_contents_ec;
  bit unsigned [31:0] parsedOut_sig_startOption_contents_store; //Store the value of the output from the generated RTL
  s_ENDPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_startOption_contents_store = OptionsParser.parsedOut_sig.startOption.contents)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_startOption_contents_store == parsed.startOption.contents;
endproperty

s_ENDPARSING_to_s_DONE_a_parsedOut_sig_startOption_optiontype_ec: assert property (disable iff(rst) s_ENDPARSING_to_s_DONE_p_parsedOut_sig_startOption_optiontype_ec);
property s_ENDPARSING_to_s_DONE_p_parsedOut_sig_startOption_optiontype_ec;
  e_options parsedOut_sig_startOption_optiontype_store; //Store the value of the output from the generated RTL
  s_ENDPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_startOption_optiontype_store = OptionsParser.parsedOut_sig.startOption.optiontype)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_startOption_optiontype_store == parsed.startOption.OptionType;
endproperty

s_ENDPARSING_to_s_DONE_a_parsedOut_sig_endOption_position_ec: assert property (disable iff(rst) s_ENDPARSING_to_s_DONE_p_parsedOut_sig_endOption_position_ec);
property s_ENDPARSING_to_s_DONE_p_parsedOut_sig_endOption_position_ec;
  bit unsigned [31:0] parsedOut_sig_endOption_position_store; //Store the value of the output from the generated RTL
  s_ENDPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_endOption_position_store = OptionsParser.parsedOut_sig.endOption.position)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_endOption_position_store == parsed.endOption.position;
endproperty

s_ENDPARSING_to_s_DONE_a_parsedOut_sig_endOption_contents_ec: assert property (disable iff(rst) s_ENDPARSING_to_s_DONE_p_parsedOut_sig_endOption_contents_ec);
property s_ENDPARSING_to_s_DONE_p_parsedOut_sig_endOption_contents_ec;
  bit unsigned [31:0] parsedOut_sig_endOption_contents_store; //Store the value of the output from the generated RTL
  s_ENDPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_endOption_contents_store = OptionsParser.parsedOut_sig.endOption.contents)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_endOption_contents_store == parsed.endOption.contents;
endproperty

s_ENDPARSING_to_s_DONE_a_parsedOut_sig_endOption_optiontype_ec: assert property (disable iff(rst) s_ENDPARSING_to_s_DONE_p_parsedOut_sig_endOption_optiontype_ec);
property s_ENDPARSING_to_s_DONE_p_parsedOut_sig_endOption_optiontype_ec;
  e_options parsedOut_sig_endOption_optiontype_store; //Store the value of the output from the generated RTL
  s_ENDPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_endOption_optiontype_store = OptionsParser.parsedOut_sig.endOption.optiontype)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_endOption_optiontype_store == parsed.endOption.OptionType;
endproperty

s_ENDPARSING_to_s_DONE_a_parsedOut_sig_infoOption_position_ec: assert property (disable iff(rst) s_ENDPARSING_to_s_DONE_p_parsedOut_sig_infoOption_position_ec);
property s_ENDPARSING_to_s_DONE_p_parsedOut_sig_infoOption_position_ec;
  bit unsigned [31:0] parsedOut_sig_infoOption_position_store; //Store the value of the output from the generated RTL
  s_ENDPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_infoOption_position_store = OptionsParser.parsedOut_sig.infoOption.position)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_infoOption_position_store == parsed.infoOption.position;
endproperty

s_ENDPARSING_to_s_DONE_a_parsedOut_sig_infoOption_contents_ec: assert property (disable iff(rst) s_ENDPARSING_to_s_DONE_p_parsedOut_sig_infoOption_contents_ec);
property s_ENDPARSING_to_s_DONE_p_parsedOut_sig_infoOption_contents_ec;
  bit unsigned [31:0] parsedOut_sig_infoOption_contents_store; //Store the value of the output from the generated RTL
  s_ENDPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_infoOption_contents_store = OptionsParser.parsedOut_sig.infoOption.contents)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_infoOption_contents_store == parsed.infoOption.contents;
endproperty

s_ENDPARSING_to_s_DONE_a_parsedOut_sig_infoOption_optiontype_ec: assert property (disable iff(rst) s_ENDPARSING_to_s_DONE_p_parsedOut_sig_infoOption_optiontype_ec);
property s_ENDPARSING_to_s_DONE_p_parsedOut_sig_infoOption_optiontype_ec;
  e_options parsedOut_sig_infoOption_optiontype_store; //Store the value of the output from the generated RTL
  s_ENDPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_infoOption_optiontype_store = OptionsParser.parsedOut_sig.infoOption.optiontype)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_infoOption_optiontype_store == parsed.infoOption.OptionType;
endproperty

s_ENDPARSING_to_s_DONE_a_parsedOut_sig_infoOptionContents_position_ec: assert property (disable iff(rst) s_ENDPARSING_to_s_DONE_p_parsedOut_sig_infoOptionContents_position_ec);
property s_ENDPARSING_to_s_DONE_p_parsedOut_sig_infoOptionContents_position_ec;
  bit unsigned [31:0] parsedOut_sig_infoOptionContents_position_store; //Store the value of the output from the generated RTL
  s_ENDPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_infoOptionContents_position_store = OptionsParser.parsedOut_sig.infoOptionContents.position)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_infoOptionContents_position_store == parsed.infoOptionContents.position;
endproperty

s_ENDPARSING_to_s_DONE_a_parsedOut_sig_infoOptionContents_contents_ec: assert property (disable iff(rst) s_ENDPARSING_to_s_DONE_p_parsedOut_sig_infoOptionContents_contents_ec);
property s_ENDPARSING_to_s_DONE_p_parsedOut_sig_infoOptionContents_contents_ec;
  bit unsigned [31:0] parsedOut_sig_infoOptionContents_contents_store; //Store the value of the output from the generated RTL
  s_ENDPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_infoOptionContents_contents_store = OptionsParser.parsedOut_sig.infoOptionContents.contents)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_infoOptionContents_contents_store == parsed.infoOptionContents.contents;
endproperty

s_ENDPARSING_to_s_DONE_a_parsedOut_sig_infoOptionContents_optiontype_ec: assert property (disable iff(rst) s_ENDPARSING_to_s_DONE_p_parsedOut_sig_infoOptionContents_optiontype_ec);
property s_ENDPARSING_to_s_DONE_p_parsedOut_sig_infoOptionContents_optiontype_ec;
  e_options parsedOut_sig_infoOptionContents_optiontype_store; //Store the value of the output from the generated RTL
  s_ENDPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_infoOptionContents_optiontype_store = OptionsParser.parsedOut_sig.infoOptionContents.optiontype)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_infoOptionContents_optiontype_store == parsed.infoOptionContents.OptionType;
endproperty

s_ENDPARSING_to_s_DONE_a_parsedOut_sig_dataOption_position_ec: assert property (disable iff(rst) s_ENDPARSING_to_s_DONE_p_parsedOut_sig_dataOption_position_ec);
property s_ENDPARSING_to_s_DONE_p_parsedOut_sig_dataOption_position_ec;
  bit unsigned [31:0] parsedOut_sig_dataOption_position_store; //Store the value of the output from the generated RTL
  s_ENDPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_dataOption_position_store = OptionsParser.parsedOut_sig.dataOption.position)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_dataOption_position_store == parsed.dataOption.position;
endproperty

s_ENDPARSING_to_s_DONE_a_parsedOut_sig_dataOption_contents_ec: assert property (disable iff(rst) s_ENDPARSING_to_s_DONE_p_parsedOut_sig_dataOption_contents_ec);
property s_ENDPARSING_to_s_DONE_p_parsedOut_sig_dataOption_contents_ec;
  bit unsigned [31:0] parsedOut_sig_dataOption_contents_store; //Store the value of the output from the generated RTL
  s_ENDPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_dataOption_contents_store = OptionsParser.parsedOut_sig.dataOption.contents)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_dataOption_contents_store == parsed.dataOption.contents;
endproperty

s_ENDPARSING_to_s_DONE_a_parsedOut_sig_dataOption_optiontype_ec: assert property (disable iff(rst) s_ENDPARSING_to_s_DONE_p_parsedOut_sig_dataOption_optiontype_ec);
property s_ENDPARSING_to_s_DONE_p_parsedOut_sig_dataOption_optiontype_ec;
  e_options parsedOut_sig_dataOption_optiontype_store; //Store the value of the output from the generated RTL
  s_ENDPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_dataOption_optiontype_store = OptionsParser.parsedOut_sig.dataOption.optiontype)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_dataOption_optiontype_store == parsed.dataOption.OptionType;
endproperty

s_ENDPARSING_to_s_DONE_a_parsedOut_sig_dataOptionLen_position_ec: assert property (disable iff(rst) s_ENDPARSING_to_s_DONE_p_parsedOut_sig_dataOptionLen_position_ec);
property s_ENDPARSING_to_s_DONE_p_parsedOut_sig_dataOptionLen_position_ec;
  bit unsigned [31:0] parsedOut_sig_dataOptionLen_position_store; //Store the value of the output from the generated RTL
  s_ENDPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_dataOptionLen_position_store = OptionsParser.parsedOut_sig.dataOptionLen.position)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_dataOptionLen_position_store == parsed.dataOptionLen.position;
endproperty

s_ENDPARSING_to_s_DONE_a_parsedOut_sig_dataOptionLen_contents_ec: assert property (disable iff(rst) s_ENDPARSING_to_s_DONE_p_parsedOut_sig_dataOptionLen_contents_ec);
property s_ENDPARSING_to_s_DONE_p_parsedOut_sig_dataOptionLen_contents_ec;
  bit unsigned [31:0] parsedOut_sig_dataOptionLen_contents_store; //Store the value of the output from the generated RTL
  s_ENDPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_dataOptionLen_contents_store = OptionsParser.parsedOut_sig.dataOptionLen.contents)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_dataOptionLen_contents_store == parsed.dataOptionLen.contents;
endproperty

s_ENDPARSING_to_s_DONE_a_parsedOut_sig_dataOptionLen_optiontype_ec: assert property (disable iff(rst) s_ENDPARSING_to_s_DONE_p_parsedOut_sig_dataOptionLen_optiontype_ec);
property s_ENDPARSING_to_s_DONE_p_parsedOut_sig_dataOptionLen_optiontype_ec;
  e_options parsedOut_sig_dataOptionLen_optiontype_store; //Store the value of the output from the generated RTL
  s_ENDPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_dataOptionLen_optiontype_store = OptionsParser.parsedOut_sig.dataOptionLen.optiontype)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_dataOptionLen_optiontype_store == parsed.dataOptionLen.OptionType;
endproperty

s_ENDPARSING_to_s_DONE_a_parsedOut_notify_ec: assert property (disable iff(rst) s_ENDPARSING_to_s_DONE_p_parsedOut_notify_ec);
property s_ENDPARSING_to_s_DONE_p_parsedOut_notify_ec;
  bit parsedOut_notify_store; //Store the value of the output from the generated RTL
  s_ENDPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_notify_store = OptionsParser.parsedOut_notify)
  |->
  ##[0:15] parsedOut_notify_store == done;
endproperty

//Internal transition assertion, checks hsk signals
s_INFOPARSING_to_s_DATAPARSING_a_ec: assert property (disable iff(rst) s_INFOPARSING_to_s_DATAPARSING_p_ec);
property s_INFOPARSING_to_s_DATAPARSING_p_ec;
  s_INFOPARSING_to_s_DATAPARSING_p_sequence
  |->
  ##1 (ready == 0) and
  ##1 (done == 0);
endproperty

//Internal transition assertion, checks hsk signals
s_INFOPARSING_to_s_DATAPARSING_1_a_ec: assert property (disable iff(rst) s_INFOPARSING_to_s_DATAPARSING_1_p_ec);
property s_INFOPARSING_to_s_DATAPARSING_1_p_ec;
  s_INFOPARSING_to_s_DATAPARSING_1_p_sequence
  |->
  ##1 (ready == 0) and
  ##1 (done == 0);
endproperty

s_INFOPARSING_to_s_DONE_a_fieldsIn_notify_ec: assert property (disable iff(rst) s_INFOPARSING_to_s_DONE_p_fieldsIn_notify_ec);
property s_INFOPARSING_to_s_DONE_p_fieldsIn_notify_ec;
  bit fieldsIn_notify_store; //Store the value of the output from the generated RTL
  s_INFOPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, fieldsIn_notify_store = OptionsParser.fieldsIn_notify)
  |->
  ##[0:15] fieldsIn_notify_store == ready;
endproperty

s_INFOPARSING_to_s_DONE_a_parsedOut_sig_hasStart_ec: assert property (disable iff(rst) s_INFOPARSING_to_s_DONE_p_parsedOut_sig_hasStart_ec);
property s_INFOPARSING_to_s_DONE_p_parsedOut_sig_hasStart_ec;
  bit parsedOut_sig_hasStart_store; //Store the value of the output from the generated RTL
  s_INFOPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_hasStart_store = OptionsParser.parsedOut_sig.hasStart)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_hasStart_store == parsed.hasStart;
endproperty

s_INFOPARSING_to_s_DONE_a_parsedOut_sig_hasInfo_ec: assert property (disable iff(rst) s_INFOPARSING_to_s_DONE_p_parsedOut_sig_hasInfo_ec);
property s_INFOPARSING_to_s_DONE_p_parsedOut_sig_hasInfo_ec;
  bit parsedOut_sig_hasInfo_store; //Store the value of the output from the generated RTL
  s_INFOPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_hasInfo_store = OptionsParser.parsedOut_sig.hasInfo)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_hasInfo_store == parsed.hasInfo;
endproperty

s_INFOPARSING_to_s_DONE_a_parsedOut_sig_hasData_ec: assert property (disable iff(rst) s_INFOPARSING_to_s_DONE_p_parsedOut_sig_hasData_ec);
property s_INFOPARSING_to_s_DONE_p_parsedOut_sig_hasData_ec;
  bit parsedOut_sig_hasData_store; //Store the value of the output from the generated RTL
  s_INFOPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_hasData_store = OptionsParser.parsedOut_sig.hasData)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_hasData_store == parsed.hasData;
endproperty

s_INFOPARSING_to_s_DONE_a_parsedOut_sig_hasEnd_ec: assert property (disable iff(rst) s_INFOPARSING_to_s_DONE_p_parsedOut_sig_hasEnd_ec);
property s_INFOPARSING_to_s_DONE_p_parsedOut_sig_hasEnd_ec;
  bit parsedOut_sig_hasEnd_store; //Store the value of the output from the generated RTL
  s_INFOPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_hasEnd_store = OptionsParser.parsedOut_sig.hasEnd)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_hasEnd_store == parsed.hasEnd;
endproperty

s_INFOPARSING_to_s_DONE_a_parsedOut_sig_isEmpty_ec: assert property (disable iff(rst) s_INFOPARSING_to_s_DONE_p_parsedOut_sig_isEmpty_ec);
property s_INFOPARSING_to_s_DONE_p_parsedOut_sig_isEmpty_ec;
  bit parsedOut_sig_isEmpty_store; //Store the value of the output from the generated RTL
  s_INFOPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_isEmpty_store = OptionsParser.parsedOut_sig.isEmpty)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_isEmpty_store == parsed.isEmpty;
endproperty

s_INFOPARSING_to_s_DONE_a_parsedOut_sig_hasError_ec: assert property (disable iff(rst) s_INFOPARSING_to_s_DONE_p_parsedOut_sig_hasError_ec);
property s_INFOPARSING_to_s_DONE_p_parsedOut_sig_hasError_ec;
  bit parsedOut_sig_hasError_store; //Store the value of the output from the generated RTL
  s_INFOPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_hasError_store = OptionsParser.parsedOut_sig.hasError)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_hasError_store == parsed.hasError;
endproperty

s_INFOPARSING_to_s_DONE_a_parsedOut_sig_startOption_position_ec: assert property (disable iff(rst) s_INFOPARSING_to_s_DONE_p_parsedOut_sig_startOption_position_ec);
property s_INFOPARSING_to_s_DONE_p_parsedOut_sig_startOption_position_ec;
  bit unsigned [31:0] parsedOut_sig_startOption_position_store; //Store the value of the output from the generated RTL
  s_INFOPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_startOption_position_store = OptionsParser.parsedOut_sig.startOption.position)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_startOption_position_store == parsed.startOption.position;
endproperty

s_INFOPARSING_to_s_DONE_a_parsedOut_sig_startOption_contents_ec: assert property (disable iff(rst) s_INFOPARSING_to_s_DONE_p_parsedOut_sig_startOption_contents_ec);
property s_INFOPARSING_to_s_DONE_p_parsedOut_sig_startOption_contents_ec;
  bit unsigned [31:0] parsedOut_sig_startOption_contents_store; //Store the value of the output from the generated RTL
  s_INFOPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_startOption_contents_store = OptionsParser.parsedOut_sig.startOption.contents)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_startOption_contents_store == parsed.startOption.contents;
endproperty

s_INFOPARSING_to_s_DONE_a_parsedOut_sig_startOption_optiontype_ec: assert property (disable iff(rst) s_INFOPARSING_to_s_DONE_p_parsedOut_sig_startOption_optiontype_ec);
property s_INFOPARSING_to_s_DONE_p_parsedOut_sig_startOption_optiontype_ec;
  e_options parsedOut_sig_startOption_optiontype_store; //Store the value of the output from the generated RTL
  s_INFOPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_startOption_optiontype_store = OptionsParser.parsedOut_sig.startOption.optiontype)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_startOption_optiontype_store == parsed.startOption.OptionType;
endproperty

s_INFOPARSING_to_s_DONE_a_parsedOut_sig_endOption_position_ec: assert property (disable iff(rst) s_INFOPARSING_to_s_DONE_p_parsedOut_sig_endOption_position_ec);
property s_INFOPARSING_to_s_DONE_p_parsedOut_sig_endOption_position_ec;
  bit unsigned [31:0] parsedOut_sig_endOption_position_store; //Store the value of the output from the generated RTL
  s_INFOPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_endOption_position_store = OptionsParser.parsedOut_sig.endOption.position)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_endOption_position_store == parsed.endOption.position;
endproperty

s_INFOPARSING_to_s_DONE_a_parsedOut_sig_endOption_contents_ec: assert property (disable iff(rst) s_INFOPARSING_to_s_DONE_p_parsedOut_sig_endOption_contents_ec);
property s_INFOPARSING_to_s_DONE_p_parsedOut_sig_endOption_contents_ec;
  bit unsigned [31:0] parsedOut_sig_endOption_contents_store; //Store the value of the output from the generated RTL
  s_INFOPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_endOption_contents_store = OptionsParser.parsedOut_sig.endOption.contents)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_endOption_contents_store == parsed.endOption.contents;
endproperty

s_INFOPARSING_to_s_DONE_a_parsedOut_sig_endOption_optiontype_ec: assert property (disable iff(rst) s_INFOPARSING_to_s_DONE_p_parsedOut_sig_endOption_optiontype_ec);
property s_INFOPARSING_to_s_DONE_p_parsedOut_sig_endOption_optiontype_ec;
  e_options parsedOut_sig_endOption_optiontype_store; //Store the value of the output from the generated RTL
  s_INFOPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_endOption_optiontype_store = OptionsParser.parsedOut_sig.endOption.optiontype)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_endOption_optiontype_store == parsed.endOption.OptionType;
endproperty

s_INFOPARSING_to_s_DONE_a_parsedOut_sig_infoOption_position_ec: assert property (disable iff(rst) s_INFOPARSING_to_s_DONE_p_parsedOut_sig_infoOption_position_ec);
property s_INFOPARSING_to_s_DONE_p_parsedOut_sig_infoOption_position_ec;
  bit unsigned [31:0] parsedOut_sig_infoOption_position_store; //Store the value of the output from the generated RTL
  s_INFOPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_infoOption_position_store = OptionsParser.parsedOut_sig.infoOption.position)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_infoOption_position_store == parsed.infoOption.position;
endproperty

s_INFOPARSING_to_s_DONE_a_parsedOut_sig_infoOption_contents_ec: assert property (disable iff(rst) s_INFOPARSING_to_s_DONE_p_parsedOut_sig_infoOption_contents_ec);
property s_INFOPARSING_to_s_DONE_p_parsedOut_sig_infoOption_contents_ec;
  bit unsigned [31:0] parsedOut_sig_infoOption_contents_store; //Store the value of the output from the generated RTL
  s_INFOPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_infoOption_contents_store = OptionsParser.parsedOut_sig.infoOption.contents)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_infoOption_contents_store == parsed.infoOption.contents;
endproperty

s_INFOPARSING_to_s_DONE_a_parsedOut_sig_infoOption_optiontype_ec: assert property (disable iff(rst) s_INFOPARSING_to_s_DONE_p_parsedOut_sig_infoOption_optiontype_ec);
property s_INFOPARSING_to_s_DONE_p_parsedOut_sig_infoOption_optiontype_ec;
  e_options parsedOut_sig_infoOption_optiontype_store; //Store the value of the output from the generated RTL
  s_INFOPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_infoOption_optiontype_store = OptionsParser.parsedOut_sig.infoOption.optiontype)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_infoOption_optiontype_store == parsed.infoOption.OptionType;
endproperty

s_INFOPARSING_to_s_DONE_a_parsedOut_sig_infoOptionContents_position_ec: assert property (disable iff(rst) s_INFOPARSING_to_s_DONE_p_parsedOut_sig_infoOptionContents_position_ec);
property s_INFOPARSING_to_s_DONE_p_parsedOut_sig_infoOptionContents_position_ec;
  bit unsigned [31:0] parsedOut_sig_infoOptionContents_position_store; //Store the value of the output from the generated RTL
  s_INFOPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_infoOptionContents_position_store = OptionsParser.parsedOut_sig.infoOptionContents.position)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_infoOptionContents_position_store == parsed.infoOptionContents.position;
endproperty

s_INFOPARSING_to_s_DONE_a_parsedOut_sig_infoOptionContents_contents_ec: assert property (disable iff(rst) s_INFOPARSING_to_s_DONE_p_parsedOut_sig_infoOptionContents_contents_ec);
property s_INFOPARSING_to_s_DONE_p_parsedOut_sig_infoOptionContents_contents_ec;
  bit unsigned [31:0] parsedOut_sig_infoOptionContents_contents_store; //Store the value of the output from the generated RTL
  s_INFOPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_infoOptionContents_contents_store = OptionsParser.parsedOut_sig.infoOptionContents.contents)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_infoOptionContents_contents_store == parsed.infoOptionContents.contents;
endproperty

s_INFOPARSING_to_s_DONE_a_parsedOut_sig_infoOptionContents_optiontype_ec: assert property (disable iff(rst) s_INFOPARSING_to_s_DONE_p_parsedOut_sig_infoOptionContents_optiontype_ec);
property s_INFOPARSING_to_s_DONE_p_parsedOut_sig_infoOptionContents_optiontype_ec;
  e_options parsedOut_sig_infoOptionContents_optiontype_store; //Store the value of the output from the generated RTL
  s_INFOPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_infoOptionContents_optiontype_store = OptionsParser.parsedOut_sig.infoOptionContents.optiontype)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_infoOptionContents_optiontype_store == parsed.infoOptionContents.OptionType;
endproperty

s_INFOPARSING_to_s_DONE_a_parsedOut_sig_dataOption_position_ec: assert property (disable iff(rst) s_INFOPARSING_to_s_DONE_p_parsedOut_sig_dataOption_position_ec);
property s_INFOPARSING_to_s_DONE_p_parsedOut_sig_dataOption_position_ec;
  bit unsigned [31:0] parsedOut_sig_dataOption_position_store; //Store the value of the output from the generated RTL
  s_INFOPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_dataOption_position_store = OptionsParser.parsedOut_sig.dataOption.position)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_dataOption_position_store == parsed.dataOption.position;
endproperty

s_INFOPARSING_to_s_DONE_a_parsedOut_sig_dataOption_contents_ec: assert property (disable iff(rst) s_INFOPARSING_to_s_DONE_p_parsedOut_sig_dataOption_contents_ec);
property s_INFOPARSING_to_s_DONE_p_parsedOut_sig_dataOption_contents_ec;
  bit unsigned [31:0] parsedOut_sig_dataOption_contents_store; //Store the value of the output from the generated RTL
  s_INFOPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_dataOption_contents_store = OptionsParser.parsedOut_sig.dataOption.contents)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_dataOption_contents_store == parsed.dataOption.contents;
endproperty

s_INFOPARSING_to_s_DONE_a_parsedOut_sig_dataOption_optiontype_ec: assert property (disable iff(rst) s_INFOPARSING_to_s_DONE_p_parsedOut_sig_dataOption_optiontype_ec);
property s_INFOPARSING_to_s_DONE_p_parsedOut_sig_dataOption_optiontype_ec;
  e_options parsedOut_sig_dataOption_optiontype_store; //Store the value of the output from the generated RTL
  s_INFOPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_dataOption_optiontype_store = OptionsParser.parsedOut_sig.dataOption.optiontype)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_dataOption_optiontype_store == parsed.dataOption.OptionType;
endproperty

s_INFOPARSING_to_s_DONE_a_parsedOut_sig_dataOptionLen_position_ec: assert property (disable iff(rst) s_INFOPARSING_to_s_DONE_p_parsedOut_sig_dataOptionLen_position_ec);
property s_INFOPARSING_to_s_DONE_p_parsedOut_sig_dataOptionLen_position_ec;
  bit unsigned [31:0] parsedOut_sig_dataOptionLen_position_store; //Store the value of the output from the generated RTL
  s_INFOPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_dataOptionLen_position_store = OptionsParser.parsedOut_sig.dataOptionLen.position)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_dataOptionLen_position_store == parsed.dataOptionLen.position;
endproperty

s_INFOPARSING_to_s_DONE_a_parsedOut_sig_dataOptionLen_contents_ec: assert property (disable iff(rst) s_INFOPARSING_to_s_DONE_p_parsedOut_sig_dataOptionLen_contents_ec);
property s_INFOPARSING_to_s_DONE_p_parsedOut_sig_dataOptionLen_contents_ec;
  bit unsigned [31:0] parsedOut_sig_dataOptionLen_contents_store; //Store the value of the output from the generated RTL
  s_INFOPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_dataOptionLen_contents_store = OptionsParser.parsedOut_sig.dataOptionLen.contents)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_dataOptionLen_contents_store == parsed.dataOptionLen.contents;
endproperty

s_INFOPARSING_to_s_DONE_a_parsedOut_sig_dataOptionLen_optiontype_ec: assert property (disable iff(rst) s_INFOPARSING_to_s_DONE_p_parsedOut_sig_dataOptionLen_optiontype_ec);
property s_INFOPARSING_to_s_DONE_p_parsedOut_sig_dataOptionLen_optiontype_ec;
  e_options parsedOut_sig_dataOptionLen_optiontype_store; //Store the value of the output from the generated RTL
  s_INFOPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_dataOptionLen_optiontype_store = OptionsParser.parsedOut_sig.dataOptionLen.optiontype)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_dataOptionLen_optiontype_store == parsed.dataOptionLen.OptionType;
endproperty

s_INFOPARSING_to_s_DONE_a_parsedOut_notify_ec: assert property (disable iff(rst) s_INFOPARSING_to_s_DONE_p_parsedOut_notify_ec);
property s_INFOPARSING_to_s_DONE_p_parsedOut_notify_ec;
  bit parsedOut_notify_store; //Store the value of the output from the generated RTL
  s_INFOPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_notify_store = OptionsParser.parsedOut_notify)
  |->
  ##[0:15] parsedOut_notify_store == done;
endproperty

//Internal transition assertion, checks hsk signals
s_INFOPARSING_to_s_ENDPARSING_a_ec: assert property (disable iff(rst) s_INFOPARSING_to_s_ENDPARSING_p_ec);
property s_INFOPARSING_to_s_ENDPARSING_p_ec;
  s_INFOPARSING_to_s_ENDPARSING_p_sequence
  |->
  ##1 (ready == 0) and
  ##1 (done == 0);
endproperty

//Internal transition assertion, checks hsk signals
s_INFOPARSING_to_s_INFOPARSING_a_ec: assert property (disable iff(rst) s_INFOPARSING_to_s_INFOPARSING_p_ec);
property s_INFOPARSING_to_s_INFOPARSING_p_ec;
  s_INFOPARSING_to_s_INFOPARSING_p_sequence
  |->
  ##1 (ready == 0) and
  ##1 (done == 0);
endproperty

//Internal transition assertion, checks hsk signals
s_INFOPARSING_to_s_INFOPARSING_1_a_ec: assert property (disable iff(rst) s_INFOPARSING_to_s_INFOPARSING_1_p_ec);
property s_INFOPARSING_to_s_INFOPARSING_1_p_ec;
  s_INFOPARSING_to_s_INFOPARSING_1_p_sequence
  |->
  ##1 (ready == 0) and
  ##1 (done == 0);
endproperty

//Internal transition assertion, checks hsk signals
s_READY_to_s_STARTPARSING_a_ec: assert property (disable iff(rst) s_READY_to_s_STARTPARSING_p_ec);
property s_READY_to_s_STARTPARSING_p_ec;
  s_READY_to_s_STARTPARSING_p_sequence
  |->
  ##1 (ready == 0) and
  ##1 (done == 0);
endproperty

//Internal transition assertion, checks hsk signals
s_STARTPARSING_to_s_DATAPARSING_a_ec: assert property (disable iff(rst) s_STARTPARSING_to_s_DATAPARSING_p_ec);
property s_STARTPARSING_to_s_DATAPARSING_p_ec;
  s_STARTPARSING_to_s_DATAPARSING_p_sequence
  |->
  ##1 (ready == 0) and
  ##1 (done == 0);
endproperty

//Internal transition assertion, checks hsk signals
s_STARTPARSING_to_s_DATAPARSING_1_a_ec: assert property (disable iff(rst) s_STARTPARSING_to_s_DATAPARSING_1_p_ec);
property s_STARTPARSING_to_s_DATAPARSING_1_p_ec;
  s_STARTPARSING_to_s_DATAPARSING_1_p_sequence
  |->
  ##1 (ready == 0) and
  ##1 (done == 0);
endproperty

s_STARTPARSING_to_s_DONE_a_fieldsIn_notify_ec: assert property (disable iff(rst) s_STARTPARSING_to_s_DONE_p_fieldsIn_notify_ec);
property s_STARTPARSING_to_s_DONE_p_fieldsIn_notify_ec;
  bit fieldsIn_notify_store; //Store the value of the output from the generated RTL
  s_STARTPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, fieldsIn_notify_store = OptionsParser.fieldsIn_notify)
  |->
  ##[0:15] fieldsIn_notify_store == ready;
endproperty

s_STARTPARSING_to_s_DONE_a_parsedOut_sig_hasStart_ec: assert property (disable iff(rst) s_STARTPARSING_to_s_DONE_p_parsedOut_sig_hasStart_ec);
property s_STARTPARSING_to_s_DONE_p_parsedOut_sig_hasStart_ec;
  bit parsedOut_sig_hasStart_store; //Store the value of the output from the generated RTL
  s_STARTPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_hasStart_store = OptionsParser.parsedOut_sig.hasStart)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_hasStart_store == parsed.hasStart;
endproperty

s_STARTPARSING_to_s_DONE_a_parsedOut_sig_hasInfo_ec: assert property (disable iff(rst) s_STARTPARSING_to_s_DONE_p_parsedOut_sig_hasInfo_ec);
property s_STARTPARSING_to_s_DONE_p_parsedOut_sig_hasInfo_ec;
  bit parsedOut_sig_hasInfo_store; //Store the value of the output from the generated RTL
  s_STARTPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_hasInfo_store = OptionsParser.parsedOut_sig.hasInfo)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_hasInfo_store == parsed.hasInfo;
endproperty

s_STARTPARSING_to_s_DONE_a_parsedOut_sig_hasData_ec: assert property (disable iff(rst) s_STARTPARSING_to_s_DONE_p_parsedOut_sig_hasData_ec);
property s_STARTPARSING_to_s_DONE_p_parsedOut_sig_hasData_ec;
  bit parsedOut_sig_hasData_store; //Store the value of the output from the generated RTL
  s_STARTPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_hasData_store = OptionsParser.parsedOut_sig.hasData)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_hasData_store == parsed.hasData;
endproperty

s_STARTPARSING_to_s_DONE_a_parsedOut_sig_hasEnd_ec: assert property (disable iff(rst) s_STARTPARSING_to_s_DONE_p_parsedOut_sig_hasEnd_ec);
property s_STARTPARSING_to_s_DONE_p_parsedOut_sig_hasEnd_ec;
  bit parsedOut_sig_hasEnd_store; //Store the value of the output from the generated RTL
  s_STARTPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_hasEnd_store = OptionsParser.parsedOut_sig.hasEnd)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_hasEnd_store == parsed.hasEnd;
endproperty

s_STARTPARSING_to_s_DONE_a_parsedOut_sig_isEmpty_ec: assert property (disable iff(rst) s_STARTPARSING_to_s_DONE_p_parsedOut_sig_isEmpty_ec);
property s_STARTPARSING_to_s_DONE_p_parsedOut_sig_isEmpty_ec;
  bit parsedOut_sig_isEmpty_store; //Store the value of the output from the generated RTL
  s_STARTPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_isEmpty_store = OptionsParser.parsedOut_sig.isEmpty)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_isEmpty_store == parsed.isEmpty;
endproperty

s_STARTPARSING_to_s_DONE_a_parsedOut_sig_hasError_ec: assert property (disable iff(rst) s_STARTPARSING_to_s_DONE_p_parsedOut_sig_hasError_ec);
property s_STARTPARSING_to_s_DONE_p_parsedOut_sig_hasError_ec;
  bit parsedOut_sig_hasError_store; //Store the value of the output from the generated RTL
  s_STARTPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_hasError_store = OptionsParser.parsedOut_sig.hasError)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_hasError_store == parsed.hasError;
endproperty

s_STARTPARSING_to_s_DONE_a_parsedOut_sig_startOption_position_ec: assert property (disable iff(rst) s_STARTPARSING_to_s_DONE_p_parsedOut_sig_startOption_position_ec);
property s_STARTPARSING_to_s_DONE_p_parsedOut_sig_startOption_position_ec;
  bit unsigned [31:0] parsedOut_sig_startOption_position_store; //Store the value of the output from the generated RTL
  s_STARTPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_startOption_position_store = OptionsParser.parsedOut_sig.startOption.position)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_startOption_position_store == parsed.startOption.position;
endproperty

s_STARTPARSING_to_s_DONE_a_parsedOut_sig_startOption_contents_ec: assert property (disable iff(rst) s_STARTPARSING_to_s_DONE_p_parsedOut_sig_startOption_contents_ec);
property s_STARTPARSING_to_s_DONE_p_parsedOut_sig_startOption_contents_ec;
  bit unsigned [31:0] parsedOut_sig_startOption_contents_store; //Store the value of the output from the generated RTL
  s_STARTPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_startOption_contents_store = OptionsParser.parsedOut_sig.startOption.contents)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_startOption_contents_store == parsed.startOption.contents;
endproperty

s_STARTPARSING_to_s_DONE_a_parsedOut_sig_startOption_optiontype_ec: assert property (disable iff(rst) s_STARTPARSING_to_s_DONE_p_parsedOut_sig_startOption_optiontype_ec);
property s_STARTPARSING_to_s_DONE_p_parsedOut_sig_startOption_optiontype_ec;
  e_options parsedOut_sig_startOption_optiontype_store; //Store the value of the output from the generated RTL
  s_STARTPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_startOption_optiontype_store = OptionsParser.parsedOut_sig.startOption.optiontype)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_startOption_optiontype_store == parsed.startOption.OptionType;
endproperty

s_STARTPARSING_to_s_DONE_a_parsedOut_sig_endOption_position_ec: assert property (disable iff(rst) s_STARTPARSING_to_s_DONE_p_parsedOut_sig_endOption_position_ec);
property s_STARTPARSING_to_s_DONE_p_parsedOut_sig_endOption_position_ec;
  bit unsigned [31:0] parsedOut_sig_endOption_position_store; //Store the value of the output from the generated RTL
  s_STARTPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_endOption_position_store = OptionsParser.parsedOut_sig.endOption.position)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_endOption_position_store == parsed.endOption.position;
endproperty

s_STARTPARSING_to_s_DONE_a_parsedOut_sig_endOption_contents_ec: assert property (disable iff(rst) s_STARTPARSING_to_s_DONE_p_parsedOut_sig_endOption_contents_ec);
property s_STARTPARSING_to_s_DONE_p_parsedOut_sig_endOption_contents_ec;
  bit unsigned [31:0] parsedOut_sig_endOption_contents_store; //Store the value of the output from the generated RTL
  s_STARTPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_endOption_contents_store = OptionsParser.parsedOut_sig.endOption.contents)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_endOption_contents_store == parsed.endOption.contents;
endproperty

s_STARTPARSING_to_s_DONE_a_parsedOut_sig_endOption_optiontype_ec: assert property (disable iff(rst) s_STARTPARSING_to_s_DONE_p_parsedOut_sig_endOption_optiontype_ec);
property s_STARTPARSING_to_s_DONE_p_parsedOut_sig_endOption_optiontype_ec;
  e_options parsedOut_sig_endOption_optiontype_store; //Store the value of the output from the generated RTL
  s_STARTPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_endOption_optiontype_store = OptionsParser.parsedOut_sig.endOption.optiontype)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_endOption_optiontype_store == parsed.endOption.OptionType;
endproperty

s_STARTPARSING_to_s_DONE_a_parsedOut_sig_infoOption_position_ec: assert property (disable iff(rst) s_STARTPARSING_to_s_DONE_p_parsedOut_sig_infoOption_position_ec);
property s_STARTPARSING_to_s_DONE_p_parsedOut_sig_infoOption_position_ec;
  bit unsigned [31:0] parsedOut_sig_infoOption_position_store; //Store the value of the output from the generated RTL
  s_STARTPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_infoOption_position_store = OptionsParser.parsedOut_sig.infoOption.position)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_infoOption_position_store == parsed.infoOption.position;
endproperty

s_STARTPARSING_to_s_DONE_a_parsedOut_sig_infoOption_contents_ec: assert property (disable iff(rst) s_STARTPARSING_to_s_DONE_p_parsedOut_sig_infoOption_contents_ec);
property s_STARTPARSING_to_s_DONE_p_parsedOut_sig_infoOption_contents_ec;
  bit unsigned [31:0] parsedOut_sig_infoOption_contents_store; //Store the value of the output from the generated RTL
  s_STARTPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_infoOption_contents_store = OptionsParser.parsedOut_sig.infoOption.contents)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_infoOption_contents_store == parsed.infoOption.contents;
endproperty

s_STARTPARSING_to_s_DONE_a_parsedOut_sig_infoOption_optiontype_ec: assert property (disable iff(rst) s_STARTPARSING_to_s_DONE_p_parsedOut_sig_infoOption_optiontype_ec);
property s_STARTPARSING_to_s_DONE_p_parsedOut_sig_infoOption_optiontype_ec;
  e_options parsedOut_sig_infoOption_optiontype_store; //Store the value of the output from the generated RTL
  s_STARTPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_infoOption_optiontype_store = OptionsParser.parsedOut_sig.infoOption.optiontype)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_infoOption_optiontype_store == parsed.infoOption.OptionType;
endproperty

s_STARTPARSING_to_s_DONE_a_parsedOut_sig_infoOptionContents_position_ec: assert property (disable iff(rst) s_STARTPARSING_to_s_DONE_p_parsedOut_sig_infoOptionContents_position_ec);
property s_STARTPARSING_to_s_DONE_p_parsedOut_sig_infoOptionContents_position_ec;
  bit unsigned [31:0] parsedOut_sig_infoOptionContents_position_store; //Store the value of the output from the generated RTL
  s_STARTPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_infoOptionContents_position_store = OptionsParser.parsedOut_sig.infoOptionContents.position)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_infoOptionContents_position_store == parsed.infoOptionContents.position;
endproperty

s_STARTPARSING_to_s_DONE_a_parsedOut_sig_infoOptionContents_contents_ec: assert property (disable iff(rst) s_STARTPARSING_to_s_DONE_p_parsedOut_sig_infoOptionContents_contents_ec);
property s_STARTPARSING_to_s_DONE_p_parsedOut_sig_infoOptionContents_contents_ec;
  bit unsigned [31:0] parsedOut_sig_infoOptionContents_contents_store; //Store the value of the output from the generated RTL
  s_STARTPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_infoOptionContents_contents_store = OptionsParser.parsedOut_sig.infoOptionContents.contents)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_infoOptionContents_contents_store == parsed.infoOptionContents.contents;
endproperty

s_STARTPARSING_to_s_DONE_a_parsedOut_sig_infoOptionContents_optiontype_ec: assert property (disable iff(rst) s_STARTPARSING_to_s_DONE_p_parsedOut_sig_infoOptionContents_optiontype_ec);
property s_STARTPARSING_to_s_DONE_p_parsedOut_sig_infoOptionContents_optiontype_ec;
  e_options parsedOut_sig_infoOptionContents_optiontype_store; //Store the value of the output from the generated RTL
  s_STARTPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_infoOptionContents_optiontype_store = OptionsParser.parsedOut_sig.infoOptionContents.optiontype)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_infoOptionContents_optiontype_store == parsed.infoOptionContents.OptionType;
endproperty

s_STARTPARSING_to_s_DONE_a_parsedOut_sig_dataOption_position_ec: assert property (disable iff(rst) s_STARTPARSING_to_s_DONE_p_parsedOut_sig_dataOption_position_ec);
property s_STARTPARSING_to_s_DONE_p_parsedOut_sig_dataOption_position_ec;
  bit unsigned [31:0] parsedOut_sig_dataOption_position_store; //Store the value of the output from the generated RTL
  s_STARTPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_dataOption_position_store = OptionsParser.parsedOut_sig.dataOption.position)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_dataOption_position_store == parsed.dataOption.position;
endproperty

s_STARTPARSING_to_s_DONE_a_parsedOut_sig_dataOption_contents_ec: assert property (disable iff(rst) s_STARTPARSING_to_s_DONE_p_parsedOut_sig_dataOption_contents_ec);
property s_STARTPARSING_to_s_DONE_p_parsedOut_sig_dataOption_contents_ec;
  bit unsigned [31:0] parsedOut_sig_dataOption_contents_store; //Store the value of the output from the generated RTL
  s_STARTPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_dataOption_contents_store = OptionsParser.parsedOut_sig.dataOption.contents)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_dataOption_contents_store == parsed.dataOption.contents;
endproperty

s_STARTPARSING_to_s_DONE_a_parsedOut_sig_dataOption_optiontype_ec: assert property (disable iff(rst) s_STARTPARSING_to_s_DONE_p_parsedOut_sig_dataOption_optiontype_ec);
property s_STARTPARSING_to_s_DONE_p_parsedOut_sig_dataOption_optiontype_ec;
  e_options parsedOut_sig_dataOption_optiontype_store; //Store the value of the output from the generated RTL
  s_STARTPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_dataOption_optiontype_store = OptionsParser.parsedOut_sig.dataOption.optiontype)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_dataOption_optiontype_store == parsed.dataOption.OptionType;
endproperty

s_STARTPARSING_to_s_DONE_a_parsedOut_sig_dataOptionLen_position_ec: assert property (disable iff(rst) s_STARTPARSING_to_s_DONE_p_parsedOut_sig_dataOptionLen_position_ec);
property s_STARTPARSING_to_s_DONE_p_parsedOut_sig_dataOptionLen_position_ec;
  bit unsigned [31:0] parsedOut_sig_dataOptionLen_position_store; //Store the value of the output from the generated RTL
  s_STARTPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_dataOptionLen_position_store = OptionsParser.parsedOut_sig.dataOptionLen.position)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_dataOptionLen_position_store == parsed.dataOptionLen.position;
endproperty

s_STARTPARSING_to_s_DONE_a_parsedOut_sig_dataOptionLen_contents_ec: assert property (disable iff(rst) s_STARTPARSING_to_s_DONE_p_parsedOut_sig_dataOptionLen_contents_ec);
property s_STARTPARSING_to_s_DONE_p_parsedOut_sig_dataOptionLen_contents_ec;
  bit unsigned [31:0] parsedOut_sig_dataOptionLen_contents_store; //Store the value of the output from the generated RTL
  s_STARTPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_dataOptionLen_contents_store = OptionsParser.parsedOut_sig.dataOptionLen.contents)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_dataOptionLen_contents_store == parsed.dataOptionLen.contents;
endproperty

s_STARTPARSING_to_s_DONE_a_parsedOut_sig_dataOptionLen_optiontype_ec: assert property (disable iff(rst) s_STARTPARSING_to_s_DONE_p_parsedOut_sig_dataOptionLen_optiontype_ec);
property s_STARTPARSING_to_s_DONE_p_parsedOut_sig_dataOptionLen_optiontype_ec;
  e_options parsedOut_sig_dataOptionLen_optiontype_store; //Store the value of the output from the generated RTL
  s_STARTPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_sig_dataOptionLen_optiontype_store = OptionsParser.parsedOut_sig.dataOptionLen.optiontype)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_dataOptionLen_optiontype_store == parsed.dataOptionLen.OptionType;
endproperty

s_STARTPARSING_to_s_DONE_a_parsedOut_notify_ec: assert property (disable iff(rst) s_STARTPARSING_to_s_DONE_p_parsedOut_notify_ec);
property s_STARTPARSING_to_s_DONE_p_parsedOut_notify_ec;
  bit parsedOut_notify_store; //Store the value of the output from the generated RTL
  s_STARTPARSING_to_s_DONE_p_sequence
  ##1 (1'b1, parsedOut_notify_store = OptionsParser.parsedOut_notify)
  |->
  ##[0:15] parsedOut_notify_store == done;
endproperty

//Internal transition assertion, checks hsk signals
s_STARTPARSING_to_s_ENDPARSING_a_ec: assert property (disable iff(rst) s_STARTPARSING_to_s_ENDPARSING_p_ec);
property s_STARTPARSING_to_s_ENDPARSING_p_ec;
  s_STARTPARSING_to_s_ENDPARSING_p_sequence
  |->
  ##1 (ready == 0) and
  ##1 (done == 0);
endproperty

//Internal transition assertion, checks hsk signals
s_STARTPARSING_to_s_INFOPARSING_a_ec: assert property (disable iff(rst) s_STARTPARSING_to_s_INFOPARSING_p_ec);
property s_STARTPARSING_to_s_INFOPARSING_p_ec;
  s_STARTPARSING_to_s_INFOPARSING_p_sequence
  |->
  ##1 (ready == 0) and
  ##1 (done == 0);
endproperty

//Internal transition assertion, checks hsk signals
s_STARTPARSING_to_s_STARTPARSING_a_ec: assert property (disable iff(rst) s_STARTPARSING_to_s_STARTPARSING_p_ec);
property s_STARTPARSING_to_s_STARTPARSING_p_ec;
  s_STARTPARSING_to_s_STARTPARSING_p_sequence
  |->
  ##1 (ready == 0) and
  ##1 (done == 0);
endproperty

s_DONE_wait_a_fieldsIn_notify_ec: assert property (disable iff(rst) s_DONE_wait_p_fieldsIn_notify_ec);
property s_DONE_wait_p_fieldsIn_notify_ec;
  bit fieldsIn_notify_store; //Store the value of the output from the generated RTL
  s_DONE_wait_p_sequence
  ##1 (1'b1, fieldsIn_notify_store = OptionsParser.fieldsIn_notify)
  |->
  ##[0:15] fieldsIn_notify_store == ready;
endproperty

s_DONE_wait_a_parsedOut_sig_hasStart_ec: assert property (disable iff(rst) s_DONE_wait_p_parsedOut_sig_hasStart_ec);
property s_DONE_wait_p_parsedOut_sig_hasStart_ec;
  bit parsedOut_sig_hasStart_store; //Store the value of the output from the generated RTL
  s_DONE_wait_p_sequence
  ##1 (1'b1, parsedOut_sig_hasStart_store = OptionsParser.parsedOut_sig.hasStart)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_hasStart_store == parsed.hasStart;
endproperty

s_DONE_wait_a_parsedOut_sig_hasInfo_ec: assert property (disable iff(rst) s_DONE_wait_p_parsedOut_sig_hasInfo_ec);
property s_DONE_wait_p_parsedOut_sig_hasInfo_ec;
  bit parsedOut_sig_hasInfo_store; //Store the value of the output from the generated RTL
  s_DONE_wait_p_sequence
  ##1 (1'b1, parsedOut_sig_hasInfo_store = OptionsParser.parsedOut_sig.hasInfo)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_hasInfo_store == parsed.hasInfo;
endproperty

s_DONE_wait_a_parsedOut_sig_hasData_ec: assert property (disable iff(rst) s_DONE_wait_p_parsedOut_sig_hasData_ec);
property s_DONE_wait_p_parsedOut_sig_hasData_ec;
  bit parsedOut_sig_hasData_store; //Store the value of the output from the generated RTL
  s_DONE_wait_p_sequence
  ##1 (1'b1, parsedOut_sig_hasData_store = OptionsParser.parsedOut_sig.hasData)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_hasData_store == parsed.hasData;
endproperty

s_DONE_wait_a_parsedOut_sig_hasEnd_ec: assert property (disable iff(rst) s_DONE_wait_p_parsedOut_sig_hasEnd_ec);
property s_DONE_wait_p_parsedOut_sig_hasEnd_ec;
  bit parsedOut_sig_hasEnd_store; //Store the value of the output from the generated RTL
  s_DONE_wait_p_sequence
  ##1 (1'b1, parsedOut_sig_hasEnd_store = OptionsParser.parsedOut_sig.hasEnd)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_hasEnd_store == parsed.hasEnd;
endproperty

s_DONE_wait_a_parsedOut_sig_isEmpty_ec: assert property (disable iff(rst) s_DONE_wait_p_parsedOut_sig_isEmpty_ec);
property s_DONE_wait_p_parsedOut_sig_isEmpty_ec;
  bit parsedOut_sig_isEmpty_store; //Store the value of the output from the generated RTL
  s_DONE_wait_p_sequence
  ##1 (1'b1, parsedOut_sig_isEmpty_store = OptionsParser.parsedOut_sig.isEmpty)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_isEmpty_store == parsed.isEmpty;
endproperty

s_DONE_wait_a_parsedOut_sig_hasError_ec: assert property (disable iff(rst) s_DONE_wait_p_parsedOut_sig_hasError_ec);
property s_DONE_wait_p_parsedOut_sig_hasError_ec;
  bit parsedOut_sig_hasError_store; //Store the value of the output from the generated RTL
  s_DONE_wait_p_sequence
  ##1 (1'b1, parsedOut_sig_hasError_store = OptionsParser.parsedOut_sig.hasError)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_hasError_store == parsed.hasError;
endproperty

s_DONE_wait_a_parsedOut_sig_startOption_position_ec: assert property (disable iff(rst) s_DONE_wait_p_parsedOut_sig_startOption_position_ec);
property s_DONE_wait_p_parsedOut_sig_startOption_position_ec;
  bit unsigned [31:0] parsedOut_sig_startOption_position_store; //Store the value of the output from the generated RTL
  s_DONE_wait_p_sequence
  ##1 (1'b1, parsedOut_sig_startOption_position_store = OptionsParser.parsedOut_sig.startOption.position)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_startOption_position_store == parsed.startOption.position;
endproperty

s_DONE_wait_a_parsedOut_sig_startOption_contents_ec: assert property (disable iff(rst) s_DONE_wait_p_parsedOut_sig_startOption_contents_ec);
property s_DONE_wait_p_parsedOut_sig_startOption_contents_ec;
  bit unsigned [31:0] parsedOut_sig_startOption_contents_store; //Store the value of the output from the generated RTL
  s_DONE_wait_p_sequence
  ##1 (1'b1, parsedOut_sig_startOption_contents_store = OptionsParser.parsedOut_sig.startOption.contents)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_startOption_contents_store == parsed.startOption.contents;
endproperty

s_DONE_wait_a_parsedOut_sig_startOption_optiontype_ec: assert property (disable iff(rst) s_DONE_wait_p_parsedOut_sig_startOption_optiontype_ec);
property s_DONE_wait_p_parsedOut_sig_startOption_optiontype_ec;
  e_options parsedOut_sig_startOption_optiontype_store; //Store the value of the output from the generated RTL
  s_DONE_wait_p_sequence
  ##1 (1'b1, parsedOut_sig_startOption_optiontype_store = OptionsParser.parsedOut_sig.startOption.optiontype)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_startOption_optiontype_store == parsed.startOption.OptionType;
endproperty

s_DONE_wait_a_parsedOut_sig_endOption_position_ec: assert property (disable iff(rst) s_DONE_wait_p_parsedOut_sig_endOption_position_ec);
property s_DONE_wait_p_parsedOut_sig_endOption_position_ec;
  bit unsigned [31:0] parsedOut_sig_endOption_position_store; //Store the value of the output from the generated RTL
  s_DONE_wait_p_sequence
  ##1 (1'b1, parsedOut_sig_endOption_position_store = OptionsParser.parsedOut_sig.endOption.position)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_endOption_position_store == parsed.endOption.position;
endproperty

s_DONE_wait_a_parsedOut_sig_endOption_contents_ec: assert property (disable iff(rst) s_DONE_wait_p_parsedOut_sig_endOption_contents_ec);
property s_DONE_wait_p_parsedOut_sig_endOption_contents_ec;
  bit unsigned [31:0] parsedOut_sig_endOption_contents_store; //Store the value of the output from the generated RTL
  s_DONE_wait_p_sequence
  ##1 (1'b1, parsedOut_sig_endOption_contents_store = OptionsParser.parsedOut_sig.endOption.contents)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_endOption_contents_store == parsed.endOption.contents;
endproperty

s_DONE_wait_a_parsedOut_sig_endOption_optiontype_ec: assert property (disable iff(rst) s_DONE_wait_p_parsedOut_sig_endOption_optiontype_ec);
property s_DONE_wait_p_parsedOut_sig_endOption_optiontype_ec;
  e_options parsedOut_sig_endOption_optiontype_store; //Store the value of the output from the generated RTL
  s_DONE_wait_p_sequence
  ##1 (1'b1, parsedOut_sig_endOption_optiontype_store = OptionsParser.parsedOut_sig.endOption.optiontype)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_endOption_optiontype_store == parsed.endOption.OptionType;
endproperty

s_DONE_wait_a_parsedOut_sig_infoOption_position_ec: assert property (disable iff(rst) s_DONE_wait_p_parsedOut_sig_infoOption_position_ec);
property s_DONE_wait_p_parsedOut_sig_infoOption_position_ec;
  bit unsigned [31:0] parsedOut_sig_infoOption_position_store; //Store the value of the output from the generated RTL
  s_DONE_wait_p_sequence
  ##1 (1'b1, parsedOut_sig_infoOption_position_store = OptionsParser.parsedOut_sig.infoOption.position)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_infoOption_position_store == parsed.infoOption.position;
endproperty

s_DONE_wait_a_parsedOut_sig_infoOption_contents_ec: assert property (disable iff(rst) s_DONE_wait_p_parsedOut_sig_infoOption_contents_ec);
property s_DONE_wait_p_parsedOut_sig_infoOption_contents_ec;
  bit unsigned [31:0] parsedOut_sig_infoOption_contents_store; //Store the value of the output from the generated RTL
  s_DONE_wait_p_sequence
  ##1 (1'b1, parsedOut_sig_infoOption_contents_store = OptionsParser.parsedOut_sig.infoOption.contents)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_infoOption_contents_store == parsed.infoOption.contents;
endproperty

s_DONE_wait_a_parsedOut_sig_infoOption_optiontype_ec: assert property (disable iff(rst) s_DONE_wait_p_parsedOut_sig_infoOption_optiontype_ec);
property s_DONE_wait_p_parsedOut_sig_infoOption_optiontype_ec;
  e_options parsedOut_sig_infoOption_optiontype_store; //Store the value of the output from the generated RTL
  s_DONE_wait_p_sequence
  ##1 (1'b1, parsedOut_sig_infoOption_optiontype_store = OptionsParser.parsedOut_sig.infoOption.optiontype)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_infoOption_optiontype_store == parsed.infoOption.OptionType;
endproperty

s_DONE_wait_a_parsedOut_sig_infoOptionContents_position_ec: assert property (disable iff(rst) s_DONE_wait_p_parsedOut_sig_infoOptionContents_position_ec);
property s_DONE_wait_p_parsedOut_sig_infoOptionContents_position_ec;
  bit unsigned [31:0] parsedOut_sig_infoOptionContents_position_store; //Store the value of the output from the generated RTL
  s_DONE_wait_p_sequence
  ##1 (1'b1, parsedOut_sig_infoOptionContents_position_store = OptionsParser.parsedOut_sig.infoOptionContents.position)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_infoOptionContents_position_store == parsed.infoOptionContents.position;
endproperty

s_DONE_wait_a_parsedOut_sig_infoOptionContents_contents_ec: assert property (disable iff(rst) s_DONE_wait_p_parsedOut_sig_infoOptionContents_contents_ec);
property s_DONE_wait_p_parsedOut_sig_infoOptionContents_contents_ec;
  bit unsigned [31:0] parsedOut_sig_infoOptionContents_contents_store; //Store the value of the output from the generated RTL
  s_DONE_wait_p_sequence
  ##1 (1'b1, parsedOut_sig_infoOptionContents_contents_store = OptionsParser.parsedOut_sig.infoOptionContents.contents)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_infoOptionContents_contents_store == parsed.infoOptionContents.contents;
endproperty

s_DONE_wait_a_parsedOut_sig_infoOptionContents_optiontype_ec: assert property (disable iff(rst) s_DONE_wait_p_parsedOut_sig_infoOptionContents_optiontype_ec);
property s_DONE_wait_p_parsedOut_sig_infoOptionContents_optiontype_ec;
  e_options parsedOut_sig_infoOptionContents_optiontype_store; //Store the value of the output from the generated RTL
  s_DONE_wait_p_sequence
  ##1 (1'b1, parsedOut_sig_infoOptionContents_optiontype_store = OptionsParser.parsedOut_sig.infoOptionContents.optiontype)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_infoOptionContents_optiontype_store == parsed.infoOptionContents.OptionType;
endproperty

s_DONE_wait_a_parsedOut_sig_dataOption_position_ec: assert property (disable iff(rst) s_DONE_wait_p_parsedOut_sig_dataOption_position_ec);
property s_DONE_wait_p_parsedOut_sig_dataOption_position_ec;
  bit unsigned [31:0] parsedOut_sig_dataOption_position_store; //Store the value of the output from the generated RTL
  s_DONE_wait_p_sequence
  ##1 (1'b1, parsedOut_sig_dataOption_position_store = OptionsParser.parsedOut_sig.dataOption.position)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_dataOption_position_store == parsed.dataOption.position;
endproperty

s_DONE_wait_a_parsedOut_sig_dataOption_contents_ec: assert property (disable iff(rst) s_DONE_wait_p_parsedOut_sig_dataOption_contents_ec);
property s_DONE_wait_p_parsedOut_sig_dataOption_contents_ec;
  bit unsigned [31:0] parsedOut_sig_dataOption_contents_store; //Store the value of the output from the generated RTL
  s_DONE_wait_p_sequence
  ##1 (1'b1, parsedOut_sig_dataOption_contents_store = OptionsParser.parsedOut_sig.dataOption.contents)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_dataOption_contents_store == parsed.dataOption.contents;
endproperty

s_DONE_wait_a_parsedOut_sig_dataOption_optiontype_ec: assert property (disable iff(rst) s_DONE_wait_p_parsedOut_sig_dataOption_optiontype_ec);
property s_DONE_wait_p_parsedOut_sig_dataOption_optiontype_ec;
  e_options parsedOut_sig_dataOption_optiontype_store; //Store the value of the output from the generated RTL
  s_DONE_wait_p_sequence
  ##1 (1'b1, parsedOut_sig_dataOption_optiontype_store = OptionsParser.parsedOut_sig.dataOption.optiontype)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_dataOption_optiontype_store == parsed.dataOption.OptionType;
endproperty

s_DONE_wait_a_parsedOut_sig_dataOptionLen_position_ec: assert property (disable iff(rst) s_DONE_wait_p_parsedOut_sig_dataOptionLen_position_ec);
property s_DONE_wait_p_parsedOut_sig_dataOptionLen_position_ec;
  bit unsigned [31:0] parsedOut_sig_dataOptionLen_position_store; //Store the value of the output from the generated RTL
  s_DONE_wait_p_sequence
  ##1 (1'b1, parsedOut_sig_dataOptionLen_position_store = OptionsParser.parsedOut_sig.dataOptionLen.position)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_dataOptionLen_position_store == parsed.dataOptionLen.position;
endproperty

s_DONE_wait_a_parsedOut_sig_dataOptionLen_contents_ec: assert property (disable iff(rst) s_DONE_wait_p_parsedOut_sig_dataOptionLen_contents_ec);
property s_DONE_wait_p_parsedOut_sig_dataOptionLen_contents_ec;
  bit unsigned [31:0] parsedOut_sig_dataOptionLen_contents_store; //Store the value of the output from the generated RTL
  s_DONE_wait_p_sequence
  ##1 (1'b1, parsedOut_sig_dataOptionLen_contents_store = OptionsParser.parsedOut_sig.dataOptionLen.contents)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_dataOptionLen_contents_store == parsed.dataOptionLen.contents;
endproperty

s_DONE_wait_a_parsedOut_sig_dataOptionLen_optiontype_ec: assert property (disable iff(rst) s_DONE_wait_p_parsedOut_sig_dataOptionLen_optiontype_ec);
property s_DONE_wait_p_parsedOut_sig_dataOptionLen_optiontype_ec;
  e_options parsedOut_sig_dataOptionLen_optiontype_store; //Store the value of the output from the generated RTL
  s_DONE_wait_p_sequence
  ##1 (1'b1, parsedOut_sig_dataOptionLen_optiontype_store = OptionsParser.parsedOut_sig.dataOptionLen.optiontype)
  ##0 (done) [->1]
  ##0 (!ready) [->1]
  |->
  parsedOut_sig_dataOptionLen_optiontype_store == parsed.dataOptionLen.OptionType;
endproperty

s_DONE_wait_a_parsedOut_notify_ec: assert property (disable iff(rst) s_DONE_wait_p_parsedOut_notify_ec);
property s_DONE_wait_p_parsedOut_notify_ec;
  bit parsedOut_notify_store; //Store the value of the output from the generated RTL
  s_DONE_wait_p_sequence
  ##1 (1'b1, parsedOut_notify_store = OptionsParser.parsedOut_notify)
  |->
  ##[0:15] parsedOut_notify_store == done;
endproperty

s_READY_wait_a_fieldsIn_notify_ec: assert property (disable iff(rst) s_READY_wait_p_fieldsIn_notify_ec);
property s_READY_wait_p_fieldsIn_notify_ec;
  bit fieldsIn_notify_store; //Store the value of the output from the generated RTL
  s_READY_wait_p_sequence
  ##1 (1'b1, fieldsIn_notify_store = OptionsParser.fieldsIn_notify)
  |->
  ##[0:1] fieldsIn_notify_store == ready;
endproperty

s_READY_wait_a_parsedOut_notify_ec: assert property (disable iff(rst) s_READY_wait_p_parsedOut_notify_ec);
property s_READY_wait_p_parsedOut_notify_ec;
  bit parsedOut_notify_store; //Store the value of the output from the generated RTL
  s_READY_wait_p_sequence
  ##1 (1'b1, parsedOut_notify_store = OptionsParser.parsedOut_notify)
  |->
  ##[0:1] parsedOut_notify_store == done;
endproperty


endmodule