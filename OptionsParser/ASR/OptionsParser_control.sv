import global_package::*;
import OptionsParser_operations::*;


module OptionsParser_control (
  input  bit                        rst,
  input  bit                        clk,
  input  bit                        fieldsIn_sync,
  input  bit                        parsedOut_sync,
  input  e_States                   CurrentState,
  input  bit unsigned [3:0]         counter,
  input  a_sc_unsigned_8_15         fields,
  input  st_ParsedOptions           parsed,
  output OptionsParser_operations_t operation
);

  typedef enum { OptionsParser_s_READY, OptionsParser_s_STARTPARSING, OptionsParser_s_INFOPARSING, OptionsParser_s_DATAPARSING, OptionsParser_s_ENDPARSING, OptionsParser_s_DONE } OptionsParser_states_t;

  OptionsParser_states_t current_state;
  OptionsParser_states_t next_state;

  always @(current_state, fieldsIn_sync, parsedOut_sync, CurrentState, counter, fields[0], fields[10], fields[11], fields[12], fields[13], fields[14], fields[1], fields[2], fields[3], fields[4], fields[5], fields[6], fields[7], fields[8], fields[9], parsed.dataOptionLen.contents, parsed.dataOptionLen.position, parsed.hasData, parsed.hasError, parsed.hasInfo, parsed.hasStart)
  begin
    case (current_state)
      OptionsParser_s_READY:
        begin
          if (fieldsIn_sync) begin
            operation <= OptionsParser_op_s_READY_1;
            next_state <= OptionsParser_s_STARTPARSING;
          end else if (!(fieldsIn_sync)) begin
            operation <= OptionsParser_op_wait_s_READY;
            next_state <= OptionsParser_s_READY;
          end
        end
      OptionsParser_s_STARTPARSING:
        begin
          if ((counter > 4'd14)) begin
            operation <= OptionsParser_op_s_STARTPARSING_2;
            next_state <= OptionsParser_s_DONE;
          end else if ((counter <= 4'd14) && (((counter == 4'd0) ? fields[0] : ((counter == 4'd1) ? fields[1] : ((counter == 4'd2) ? fields[2] : ((counter == 4'd3) ? fields[3] : ((counter == 4'd4) ? fields[4] : ((counter == 4'd5) ? fields[5] : ((counter == 4'd6) ? fields[6] : ((counter == 4'd7) ? fields[7] : ((counter == 4'd8) ? fields[8] : ((counter == 4'd9) ? fields[9] : ((counter == 4'd10) ? fields[10] : ((counter == 4'd11) ? fields[11] : ((counter == 4'd12) ? fields[12] : ((counter == 4'd13) ? fields[13] : fields[14])))))))))))))) == 2) && parsed.hasStart) begin
            operation <= OptionsParser_op_s_STARTPARSING_3;
            next_state <= OptionsParser_s_ENDPARSING;
          end else if ((counter <= 4'd14) && !(((((counter == 4'd0) ? fields[0] : ((counter == 4'd1) ? fields[1] : ((counter == 4'd2) ? fields[2] : ((counter == 4'd3) ? fields[3] : ((counter == 4'd4) ? fields[4] : ((counter == 4'd5) ? fields[5] : ((counter == 4'd6) ? fields[6] : ((counter == 4'd7) ? fields[7] : ((counter == 4'd8) ? fields[8] : ((counter == 4'd9) ? fields[9] : ((counter == 4'd10) ? fields[10] : ((counter == 4'd11) ? fields[11] : ((counter == 4'd12) ? fields[12] : ((counter == 4'd13) ? fields[13] : fields[14])))))))))))))) == 2) && parsed.hasStart)) && (((counter == 4'd0) ? fields[0] : ((counter == 4'd1) ? fields[1] : ((counter == 4'd2) ? fields[2] : ((counter == 4'd3) ? fields[3] : ((counter == 4'd4) ? fields[4] : ((counter == 4'd5) ? fields[5] : ((counter == 4'd6) ? fields[6] : ((counter == 4'd7) ? fields[7] : ((counter == 4'd8) ? fields[8] : ((counter == 4'd9) ? fields[9] : ((counter == 4'd10) ? fields[10] : ((counter == 4'd11) ? fields[11] : ((counter == 4'd12) ? fields[12] : ((counter == 4'd13) ? fields[13] : fields[14])))))))))))))) == 3) && parsed.hasStart) begin
            operation <= OptionsParser_op_s_STARTPARSING_4;
            next_state <= OptionsParser_s_INFOPARSING;
          end else if ((counter <= 4'd14) && !(((((counter == 4'd0) ? fields[0] : ((counter == 4'd1) ? fields[1] : ((counter == 4'd2) ? fields[2] : ((counter == 4'd3) ? fields[3] : ((counter == 4'd4) ? fields[4] : ((counter == 4'd5) ? fields[5] : ((counter == 4'd6) ? fields[6] : ((counter == 4'd7) ? fields[7] : ((counter == 4'd8) ? fields[8] : ((counter == 4'd9) ? fields[9] : ((counter == 4'd10) ? fields[10] : ((counter == 4'd11) ? fields[11] : fields[14])))))))))))) == 2) && parsed.hasStart)) && !(((((counter == 4'd0) ? fields[0] : ((counter == 4'd1) ? fields[1] : ((counter == 4'd2) ? fields[2] : ((counter == 4'd3) ? fields[3] : ((counter == 4'd4) ? fields[4] : ((counter == 4'd5) ? fields[5] : ((counter == 4'd6) ? fields[6] : ((counter == 4'd7) ? fields[7] : ((counter == 4'd8) ? fields[8] : ((counter == 4'd9) ? fields[9] : ((counter == 4'd10) ? fields[10] : ((counter == 4'd11) ? fields[11] : fields[14])))))))))))) == 3) && parsed.hasStart)) && (((counter == 4'd0) ? fields[0] : ((counter == 4'd1) ? fields[1] : ((counter == 4'd2) ? fields[2] : ((counter == 4'd3) ? fields[3] : ((counter == 4'd4) ? fields[4] : ((counter == 4'd5) ? fields[5] : ((counter == 4'd6) ? fields[6] : ((counter == 4'd7) ? fields[7] : ((counter == 4'd8) ? fields[8] : ((counter == 4'd9) ? fields[9] : ((counter == 4'd10) ? fields[10] : fields[11]))))))))))) == 4) && parsed.hasStart && (counter < 4'd12) && (((((counter + 4'd1) == 5'd0) ? fields[0] : (((counter + 4'd1) == 5'd1) ? fields[1] : (((counter + 4'd1) == 5'd2) ? fields[2] : (((counter + 4'd1) == 5'd3) ? fields[3] : (((counter + 4'd1) == 5'd4) ? fields[4] : (((counter + 4'd1) == 5'd5) ? fields[5] : (((counter + 4'd1) == 5'd6) ? fields[6] : (((counter + 4'd1) == 5'd7) ? fields[7] : (((counter + 4'd1) == 5'd8) ? fields[8] : (((counter + 4'd1) == 5'd9) ? fields[9] : (((counter + 4'd1) == 5'd10) ? fields[10] : (((counter + 4'd1) == 5'd11) ? fields[11] : (((counter + 4'd1) == 5'd12) ? fields[12] : (((counter + 4'd1) == 5'd13) ? fields[13] : fields[14])))))))))))))) > 8'd5) || ((((((counter + 4'd1) == 5'd0) ? fields[0] : (((counter + 4'd1) == 5'd1) ? fields[1] : (((counter + 4'd1) == 5'd2) ? fields[2] : (((counter + 4'd1) == 5'd3) ? fields[3] : (((counter + 4'd1) == 5'd4) ? fields[4] : (((counter + 4'd1) == 5'd5) ? fields[5] : (((counter + 4'd1) == 5'd6) ? fields[6] : (((counter + 4'd1) == 5'd7) ? fields[7] : (((counter + 4'd1) == 5'd8) ? fields[8] : (((counter + 4'd1) == 5'd9) ? fields[9] : (((counter + 4'd1) == 5'd10) ? fields[10] : (((counter + 4'd1) == 5'd11) ? fields[11] : (((counter + 4'd1) == 5'd12) ? fields[12] : (((counter + 4'd1) == 5'd13) ? fields[13] : fields[14])))))))))))))) + counter) + 9'd1) > 10'd13))) begin
            operation <= OptionsParser_op_s_STARTPARSING_5;
            next_state <= OptionsParser_s_DATAPARSING;
          end else if ((counter <= 4'd14) && !(((((counter == 4'd0) ? fields[0] : ((counter == 4'd1) ? fields[1] : ((counter == 4'd2) ? fields[2] : ((counter == 4'd3) ? fields[3] : ((counter == 4'd4) ? fields[4] : ((counter == 4'd5) ? fields[5] : ((counter == 4'd6) ? fields[6] : ((counter == 4'd7) ? fields[7] : ((counter == 4'd8) ? fields[8] : ((counter == 4'd9) ? fields[9] : ((counter == 4'd10) ? fields[10] : ((counter == 4'd11) ? fields[11] : fields[14])))))))))))) == 2) && parsed.hasStart)) && !(((((counter == 4'd0) ? fields[0] : ((counter == 4'd1) ? fields[1] : ((counter == 4'd2) ? fields[2] : ((counter == 4'd3) ? fields[3] : ((counter == 4'd4) ? fields[4] : ((counter == 4'd5) ? fields[5] : ((counter == 4'd6) ? fields[6] : ((counter == 4'd7) ? fields[7] : ((counter == 4'd8) ? fields[8] : ((counter == 4'd9) ? fields[9] : ((counter == 4'd10) ? fields[10] : ((counter == 4'd11) ? fields[11] : fields[14])))))))))))) == 3) && parsed.hasStart)) && (((counter == 4'd0) ? fields[0] : ((counter == 4'd1) ? fields[1] : ((counter == 4'd2) ? fields[2] : ((counter == 4'd3) ? fields[3] : ((counter == 4'd4) ? fields[4] : ((counter == 4'd5) ? fields[5] : ((counter == 4'd6) ? fields[6] : ((counter == 4'd7) ? fields[7] : ((counter == 4'd8) ? fields[8] : ((counter == 4'd9) ? fields[9] : ((counter == 4'd10) ? fields[10] : fields[11]))))))))))) == 4) && parsed.hasStart && (counter < 4'd12) && !((((((counter + 4'd1) == 5'd0) ? fields[0] : (((counter + 4'd1) == 5'd1) ? fields[1] : (((counter + 4'd1) == 5'd2) ? fields[2] : (((counter + 4'd1) == 5'd3) ? fields[3] : (((counter + 4'd1) == 5'd4) ? fields[4] : (((counter + 4'd1) == 5'd5) ? fields[5] : (((counter + 4'd1) == 5'd6) ? fields[6] : (((counter + 4'd1) == 5'd7) ? fields[7] : (((counter + 4'd1) == 5'd8) ? fields[8] : (((counter + 4'd1) == 5'd9) ? fields[9] : (((counter + 4'd1) == 5'd10) ? fields[10] : (((counter + 4'd1) == 5'd11) ? fields[11] : (((counter + 4'd1) == 5'd12) ? fields[12] : (((counter + 4'd1) == 5'd13) ? fields[13] : fields[14])))))))))))))) > 8'd5) || ((((((counter + 4'd1) == 5'd0) ? fields[0] : (((counter + 4'd1) == 5'd1) ? fields[1] : (((counter + 4'd1) == 5'd2) ? fields[2] : (((counter + 4'd1) == 5'd3) ? fields[3] : (((counter + 4'd1) == 5'd4) ? fields[4] : (((counter + 4'd1) == 5'd5) ? fields[5] : (((counter + 4'd1) == 5'd6) ? fields[6] : (((counter + 4'd1) == 5'd7) ? fields[7] : (((counter + 4'd1) == 5'd8) ? fields[8] : (((counter + 4'd1) == 5'd9) ? fields[9] : (((counter + 4'd1) == 5'd10) ? fields[10] : (((counter + 4'd1) == 5'd11) ? fields[11] : (((counter + 4'd1) == 5'd12) ? fields[12] : (((counter + 4'd1) == 5'd13) ? fields[13] : fields[14])))))))))))))) + counter) + 9'd1) > 10'd13)))) begin
            operation <= OptionsParser_op_s_STARTPARSING_6;
            next_state <= OptionsParser_s_DATAPARSING;
          end else if ((counter <= 4'd14) && !(((((counter == 4'd0) ? fields[0] : ((counter == 4'd1) ? fields[1] : ((counter == 4'd2) ? fields[2] : ((counter == 4'd3) ? fields[3] : ((counter == 4'd4) ? fields[4] : ((counter == 4'd5) ? fields[5] : ((counter == 4'd6) ? fields[6] : ((counter == 4'd7) ? fields[7] : ((counter == 4'd8) ? fields[8] : ((counter == 4'd9) ? fields[9] : ((counter == 4'd10) ? fields[10] : ((counter == 4'd11) ? fields[11] : ((counter == 4'd12) ? fields[12] : ((counter == 4'd13) ? fields[13] : fields[14])))))))))))))) == 2) && parsed.hasStart)) && !(((((counter == 4'd0) ? fields[0] : ((counter == 4'd1) ? fields[1] : ((counter == 4'd2) ? fields[2] : ((counter == 4'd3) ? fields[3] : ((counter == 4'd4) ? fields[4] : ((counter == 4'd5) ? fields[5] : ((counter == 4'd6) ? fields[6] : ((counter == 4'd7) ? fields[7] : ((counter == 4'd8) ? fields[8] : ((counter == 4'd9) ? fields[9] : ((counter == 4'd10) ? fields[10] : ((counter == 4'd11) ? fields[11] : ((counter == 4'd12) ? fields[12] : ((counter == 4'd13) ? fields[13] : fields[14])))))))))))))) == 3) && parsed.hasStart)) && !((((((counter == 4'd0) ? fields[0] : ((counter == 4'd1) ? fields[1] : ((counter == 4'd2) ? fields[2] : ((counter == 4'd3) ? fields[3] : ((counter == 4'd4) ? fields[4] : ((counter == 4'd5) ? fields[5] : ((counter == 4'd6) ? fields[6] : ((counter == 4'd7) ? fields[7] : ((counter == 4'd8) ? fields[8] : ((counter == 4'd9) ? fields[9] : ((counter == 4'd10) ? fields[10] : fields[11]))))))))))) == 4) && parsed.hasStart) && (counter < 4'd12)))) begin
            operation <= OptionsParser_op_s_STARTPARSING_7;
            next_state <= OptionsParser_s_STARTPARSING;
          end
        end
      OptionsParser_s_INFOPARSING:
        begin
          if (!(parsed.hasInfo) && (counter < 4'd13) && (CurrentState == INFOPARSING)) begin
            operation <= OptionsParser_op_s_INFOPARSING_8;
            next_state <= OptionsParser_s_INFOPARSING;
          end else if ((parsed.hasInfo || (counter >= 4'd13)) && (counter > 4'd14)) begin
            operation <= OptionsParser_op_s_INFOPARSING_9;
            next_state <= OptionsParser_s_DONE;
          end else if ((parsed.hasInfo || (counter >= 4'd13)) && (counter <= 4'd14) && (((counter == 4'd0) ? fields[0] : ((counter == 4'd1) ? fields[1] : ((counter == 4'd2) ? fields[2] : ((counter == 4'd3) ? fields[3] : ((counter == 4'd4) ? fields[4] : ((counter == 4'd5) ? fields[5] : ((counter == 4'd6) ? fields[6] : ((counter == 4'd7) ? fields[7] : ((counter == 4'd8) ? fields[8] : ((counter == 4'd9) ? fields[9] : ((counter == 4'd10) ? fields[10] : ((counter == 4'd11) ? fields[11] : ((counter == 4'd12) ? fields[12] : ((counter == 4'd13) ? fields[13] : fields[14])))))))))))))) == 2)) begin
            operation <= OptionsParser_op_s_INFOPARSING_10;
            next_state <= OptionsParser_s_ENDPARSING;
          end else if ((parsed.hasInfo || (counter >= 4'd13)) && (counter <= 4'd14) && (((counter == 4'd0) ? fields[0] : ((counter == 4'd1) ? fields[1] : ((counter == 4'd2) ? fields[2] : ((counter == 4'd3) ? fields[3] : ((counter == 4'd4) ? fields[4] : ((counter == 4'd5) ? fields[5] : ((counter == 4'd6) ? fields[6] : ((counter == 4'd7) ? fields[7] : ((counter == 4'd8) ? fields[8] : ((counter == 4'd9) ? fields[9] : ((counter == 4'd10) ? fields[10] : ((counter == 4'd11) ? fields[11] : fields[14])))))))))))) != 2) && (((counter == 4'd0) ? fields[0] : ((counter == 4'd1) ? fields[1] : ((counter == 4'd2) ? fields[2] : ((counter == 4'd3) ? fields[3] : ((counter == 4'd4) ? fields[4] : ((counter == 4'd5) ? fields[5] : ((counter == 4'd6) ? fields[6] : ((counter == 4'd7) ? fields[7] : ((counter == 4'd8) ? fields[8] : ((counter == 4'd9) ? fields[9] : ((counter == 4'd10) ? fields[10] : fields[11]))))))))))) == 4) && !(parsed.hasData) && (counter < 4'd12) && (((((counter + 4'd1) == 5'd0) ? fields[0] : (((counter + 4'd1) == 5'd1) ? fields[1] : (((counter + 4'd1) == 5'd2) ? fields[2] : (((counter + 4'd1) == 5'd3) ? fields[3] : (((counter + 4'd1) == 5'd4) ? fields[4] : (((counter + 4'd1) == 5'd5) ? fields[5] : (((counter + 4'd1) == 5'd6) ? fields[6] : (((counter + 4'd1) == 5'd7) ? fields[7] : (((counter + 4'd1) == 5'd8) ? fields[8] : (((counter + 4'd1) == 5'd9) ? fields[9] : (((counter + 4'd1) == 5'd10) ? fields[10] : (((counter + 4'd1) == 5'd11) ? fields[11] : (((counter + 4'd1) == 5'd12) ? fields[12] : (((counter + 4'd1) == 5'd13) ? fields[13] : fields[14])))))))))))))) > 8'd5) || ((((((counter + 4'd1) == 5'd0) ? fields[0] : (((counter + 4'd1) == 5'd1) ? fields[1] : (((counter + 4'd1) == 5'd2) ? fields[2] : (((counter + 4'd1) == 5'd3) ? fields[3] : (((counter + 4'd1) == 5'd4) ? fields[4] : (((counter + 4'd1) == 5'd5) ? fields[5] : (((counter + 4'd1) == 5'd6) ? fields[6] : (((counter + 4'd1) == 5'd7) ? fields[7] : (((counter + 4'd1) == 5'd8) ? fields[8] : (((counter + 4'd1) == 5'd9) ? fields[9] : (((counter + 4'd1) == 5'd10) ? fields[10] : (((counter + 4'd1) == 5'd11) ? fields[11] : (((counter + 4'd1) == 5'd12) ? fields[12] : (((counter + 4'd1) == 5'd13) ? fields[13] : fields[14])))))))))))))) + counter) + 9'd1) > 10'd13))) begin
            operation <= OptionsParser_op_s_INFOPARSING_11;
            next_state <= OptionsParser_s_DATAPARSING;
          end else if ((parsed.hasInfo || (counter >= 4'd13)) && (counter <= 4'd14) && (((counter == 4'd0) ? fields[0] : ((counter == 4'd1) ? fields[1] : ((counter == 4'd2) ? fields[2] : ((counter == 4'd3) ? fields[3] : ((counter == 4'd4) ? fields[4] : ((counter == 4'd5) ? fields[5] : ((counter == 4'd6) ? fields[6] : ((counter == 4'd7) ? fields[7] : ((counter == 4'd8) ? fields[8] : ((counter == 4'd9) ? fields[9] : ((counter == 4'd10) ? fields[10] : ((counter == 4'd11) ? fields[11] : fields[14])))))))))))) != 2) && (((counter == 4'd0) ? fields[0] : ((counter == 4'd1) ? fields[1] : ((counter == 4'd2) ? fields[2] : ((counter == 4'd3) ? fields[3] : ((counter == 4'd4) ? fields[4] : ((counter == 4'd5) ? fields[5] : ((counter == 4'd6) ? fields[6] : ((counter == 4'd7) ? fields[7] : ((counter == 4'd8) ? fields[8] : ((counter == 4'd9) ? fields[9] : ((counter == 4'd10) ? fields[10] : fields[11]))))))))))) == 4) && !(parsed.hasData) && (counter < 4'd12) && !((((((counter + 4'd1) == 5'd0) ? fields[0] : (((counter + 4'd1) == 5'd1) ? fields[1] : (((counter + 4'd1) == 5'd2) ? fields[2] : (((counter + 4'd1) == 5'd3) ? fields[3] : (((counter + 4'd1) == 5'd4) ? fields[4] : (((counter + 4'd1) == 5'd5) ? fields[5] : (((counter + 4'd1) == 5'd6) ? fields[6] : (((counter + 4'd1) == 5'd7) ? fields[7] : (((counter + 4'd1) == 5'd8) ? fields[8] : (((counter + 4'd1) == 5'd9) ? fields[9] : (((counter + 4'd1) == 5'd10) ? fields[10] : (((counter + 4'd1) == 5'd11) ? fields[11] : (((counter + 4'd1) == 5'd12) ? fields[12] : (((counter + 4'd1) == 5'd13) ? fields[13] : fields[14])))))))))))))) > 8'd5) || ((((((counter + 4'd1) == 5'd0) ? fields[0] : (((counter + 4'd1) == 5'd1) ? fields[1] : (((counter + 4'd1) == 5'd2) ? fields[2] : (((counter + 4'd1) == 5'd3) ? fields[3] : (((counter + 4'd1) == 5'd4) ? fields[4] : (((counter + 4'd1) == 5'd5) ? fields[5] : (((counter + 4'd1) == 5'd6) ? fields[6] : (((counter + 4'd1) == 5'd7) ? fields[7] : (((counter + 4'd1) == 5'd8) ? fields[8] : (((counter + 4'd1) == 5'd9) ? fields[9] : (((counter + 4'd1) == 5'd10) ? fields[10] : (((counter + 4'd1) == 5'd11) ? fields[11] : (((counter + 4'd1) == 5'd12) ? fields[12] : (((counter + 4'd1) == 5'd13) ? fields[13] : fields[14])))))))))))))) + counter) + 9'd1) > 10'd13)))) begin
            operation <= OptionsParser_op_s_INFOPARSING_12;
            next_state <= OptionsParser_s_DATAPARSING;
          end else if ((parsed.hasInfo || (counter >= 4'd13)) && (counter <= 4'd14) && (((counter == 4'd0) ? fields[0] : ((counter == 4'd1) ? fields[1] : ((counter == 4'd2) ? fields[2] : ((counter == 4'd3) ? fields[3] : ((counter == 4'd4) ? fields[4] : ((counter == 4'd5) ? fields[5] : ((counter == 4'd6) ? fields[6] : ((counter == 4'd7) ? fields[7] : ((counter == 4'd8) ? fields[8] : ((counter == 4'd9) ? fields[9] : ((counter == 4'd10) ? fields[10] : ((counter == 4'd11) ? fields[11] : ((counter == 4'd12) ? fields[12] : ((counter == 4'd13) ? fields[13] : fields[14])))))))))))))) != 2) && !((((((counter == 4'd0) ? fields[0] : ((counter == 4'd1) ? fields[1] : ((counter == 4'd2) ? fields[2] : ((counter == 4'd3) ? fields[3] : ((counter == 4'd4) ? fields[4] : ((counter == 4'd5) ? fields[5] : ((counter == 4'd6) ? fields[6] : ((counter == 4'd7) ? fields[7] : ((counter == 4'd8) ? fields[8] : ((counter == 4'd9) ? fields[9] : ((counter == 4'd10) ? fields[10] : fields[11]))))))))))) == 4) && !(parsed.hasData)) && (counter < 4'd12)))) begin
            operation <= OptionsParser_op_s_INFOPARSING_13;
            next_state <= OptionsParser_s_INFOPARSING;
          end
        end
      OptionsParser_s_DATAPARSING:
        begin
          if (!(parsed.hasError) && !(parsed.hasData) && ((counter < 4'd13) || (((counter == 4'd13) ? fields[13] : fields[14]) == 0)) && (CurrentState == DATAPARSING)) begin
            operation <= OptionsParser_op_s_DATAPARSING_14;
            next_state <= OptionsParser_s_DATAPARSING;
          end else if (((parsed.hasError || parsed.hasData) || !(((counter < 4'd13) || (((counter == 4'd13) ? fields[13] : fields[14]) == 0)))) && ((parsed.hasError || (counter > 4'd14)) || ((parsed.dataOptionLen.contents > 8'd5) && ((parsed.dataOptionLen.position + parsed.dataOptionLen.contents) > 9'd13)))) begin
            operation <= OptionsParser_op_s_DATAPARSING_15;
            next_state <= OptionsParser_s_DONE;
          end else if (((parsed.hasError || parsed.hasData) || !(((counter < 4'd13) || (((counter == 4'd13) ? fields[13] : fields[14]) == 0)))) && !(((parsed.hasError || (counter > 4'd14)) || ((parsed.dataOptionLen.contents > 8'd5) && ((parsed.dataOptionLen.position + parsed.dataOptionLen.contents) > 9'd13)))) && parsed.hasData && (counter <= (parsed.dataOptionLen.position + parsed.dataOptionLen.contents))) begin
            operation <= OptionsParser_op_s_DATAPARSING_16;
            next_state <= OptionsParser_s_DATAPARSING;
          end else if (((parsed.hasError || parsed.hasData) || !(((counter < 4'd13) || (((counter == 4'd13) ? fields[13] : fields[14]) == 0)))) && !(((parsed.hasError || (counter > 4'd14)) || ((parsed.dataOptionLen.contents > 8'd5) && ((parsed.dataOptionLen.position + parsed.dataOptionLen.contents) > 9'd13)))) && !((parsed.hasData && (counter <= (parsed.dataOptionLen.position + parsed.dataOptionLen.contents)))) && (((counter == 4'd0) ? fields[0] : ((counter == 4'd1) ? fields[1] : ((counter == 4'd2) ? fields[2] : ((counter == 4'd3) ? fields[3] : ((counter == 4'd4) ? fields[4] : ((counter == 4'd5) ? fields[5] : ((counter == 4'd6) ? fields[6] : ((counter == 4'd7) ? fields[7] : ((counter == 4'd8) ? fields[8] : ((counter == 4'd9) ? fields[9] : ((counter == 4'd10) ? fields[10] : ((counter == 4'd11) ? fields[11] : ((counter == 4'd12) ? fields[12] : ((counter == 4'd13) ? fields[13] : fields[14])))))))))))))) == 2)) begin
            operation <= OptionsParser_op_s_DATAPARSING_17;
            next_state <= OptionsParser_s_ENDPARSING;
          end else if (((parsed.hasError || parsed.hasData) || !(((counter < 4'd13) || (((counter == 4'd13) ? fields[13] : fields[14]) == 0)))) && !(((parsed.hasError || (counter > 4'd14)) || ((parsed.dataOptionLen.contents > 8'd5) && ((parsed.dataOptionLen.position + parsed.dataOptionLen.contents) > 9'd13)))) && !((parsed.hasData && (counter <= (parsed.dataOptionLen.position + parsed.dataOptionLen.contents)))) && (((counter == 4'd0) ? fields[0] : ((counter == 4'd1) ? fields[1] : ((counter == 4'd2) ? fields[2] : ((counter == 4'd3) ? fields[3] : ((counter == 4'd4) ? fields[4] : ((counter == 4'd5) ? fields[5] : ((counter == 4'd6) ? fields[6] : ((counter == 4'd7) ? fields[7] : ((counter == 4'd8) ? fields[8] : ((counter == 4'd9) ? fields[9] : ((counter == 4'd10) ? fields[10] : ((counter == 4'd11) ? fields[11] : ((counter == 4'd12) ? fields[12] : ((counter == 4'd13) ? fields[13] : fields[14])))))))))))))) != 2) && (((counter == 4'd0) ? fields[0] : ((counter == 4'd1) ? fields[1] : ((counter == 4'd2) ? fields[2] : ((counter == 4'd3) ? fields[3] : ((counter == 4'd4) ? fields[4] : ((counter == 4'd5) ? fields[5] : ((counter == 4'd6) ? fields[6] : ((counter == 4'd7) ? fields[7] : ((counter == 4'd8) ? fields[8] : ((counter == 4'd9) ? fields[9] : ((counter == 4'd10) ? fields[10] : ((counter == 4'd11) ? fields[11] : ((counter == 4'd12) ? fields[12] : ((counter == 4'd13) ? fields[13] : fields[14])))))))))))))) == 3) && !(parsed.hasInfo)) begin
            operation <= OptionsParser_op_s_DATAPARSING_18;
            next_state <= OptionsParser_s_INFOPARSING;
          end else if (((parsed.hasError || parsed.hasData) || !(((counter < 4'd13) || (((counter == 4'd13) ? fields[13] : fields[14]) == 0)))) && !(((parsed.hasError || (counter > 4'd14)) || ((parsed.dataOptionLen.contents > 8'd5) && ((parsed.dataOptionLen.position + parsed.dataOptionLen.contents) > 9'd13)))) && !((parsed.hasData && (counter <= (parsed.dataOptionLen.position + parsed.dataOptionLen.contents)))) && (((counter == 4'd0) ? fields[0] : ((counter == 4'd1) ? fields[1] : ((counter == 4'd2) ? fields[2] : ((counter == 4'd3) ? fields[3] : ((counter == 4'd4) ? fields[4] : ((counter == 4'd5) ? fields[5] : ((counter == 4'd6) ? fields[6] : ((counter == 4'd7) ? fields[7] : ((counter == 4'd8) ? fields[8] : ((counter == 4'd9) ? fields[9] : ((counter == 4'd10) ? fields[10] : ((counter == 4'd11) ? fields[11] : ((counter == 4'd12) ? fields[12] : ((counter == 4'd13) ? fields[13] : fields[14])))))))))))))) != 2) && ((((counter == 4'd0) ? fields[0] : ((counter == 4'd1) ? fields[1] : ((counter == 4'd2) ? fields[2] : ((counter == 4'd3) ? fields[3] : ((counter == 4'd4) ? fields[4] : ((counter == 4'd5) ? fields[5] : ((counter == 4'd6) ? fields[6] : ((counter == 4'd7) ? fields[7] : ((counter == 4'd8) ? fields[8] : ((counter == 4'd9) ? fields[9] : ((counter == 4'd10) ? fields[10] : ((counter == 4'd11) ? fields[11] : ((counter == 4'd12) ? fields[12] : ((counter == 4'd13) ? fields[13] : fields[14])))))))))))))) != 3) || parsed.hasInfo) && (CurrentState == DATAPARSING)) begin
            operation <= OptionsParser_op_s_DATAPARSING_19;
            next_state <= OptionsParser_s_DATAPARSING;
          end
        end
      OptionsParser_s_ENDPARSING:
        begin
          if (1) begin
            operation <= OptionsParser_op_s_ENDPARSING_20;
            next_state <= OptionsParser_s_DONE;
          end
        end
      OptionsParser_s_DONE:
        begin
          if (parsedOut_sync) begin
            operation <= OptionsParser_op_s_DONE_21;
            next_state <= OptionsParser_s_READY;
          end else if (!(parsedOut_sync)) begin
            operation <= OptionsParser_op_wait_s_DONE;
            next_state <= OptionsParser_s_DONE;
          end
        end
    endcase
  end

  always_ff @(posedge clk)
  begin
    if (rst == 1) begin
      current_state <= OptionsParser_s_READY;
    end else begin
      current_state <= next_state;
    end
  end

endmodule
