import global_package::*;
import OptionsParser_operations::*;


module OptionsParser_computational (
  input  bit                        rst,
  input  bit                        clk,
  input  a_unsigned_32_15           fieldsIn_sig,
  output bit                        fieldsIn_notify,
  output st_ParsedOptions           parsedOut_sig,
  output bit                        parsedOut_notify,
  output e_States                   CurrentState_out,
  output bit unsigned [31:0]        counter_out,
  output a_unsigned_32_15           fields_out,
  output st_ParsedOptions           parsed_out,
  input  OptionsParser_operations_t operation
);

  e_States            CurrentState;
  bit unsigned [31:0] counter;
  a_unsigned_32_15    fields;
  st_ParsedOptions    parsed;

  always_ff @(posedge clk) begin
    if (rst)
      CurrentState <= READY;
    else begin
      if (operation == OptionsParser_op_s_DATAPARSING_16 || operation == OptionsParser_op_s_INFOPARSING_11 || operation == OptionsParser_op_s_INFOPARSING_12 || operation == OptionsParser_op_s_STARTPARSING_5 || operation == OptionsParser_op_s_STARTPARSING_6)
        CurrentState <= DATAPARSING;
      else if (operation == OptionsParser_op_s_DATAPARSING_15 || operation == OptionsParser_op_s_ENDPARSING_20 || operation == OptionsParser_op_s_INFOPARSING_9 || operation == OptionsParser_op_s_STARTPARSING_2)
        CurrentState <= DONE;
      else if (operation == OptionsParser_op_s_DATAPARSING_17 || operation == OptionsParser_op_s_INFOPARSING_10 || operation == OptionsParser_op_s_STARTPARSING_3)
        CurrentState <= ENDPARSING;
      else if (operation == OptionsParser_op_s_DATAPARSING_18 || operation == OptionsParser_op_s_INFOPARSING_13 || operation == OptionsParser_op_s_STARTPARSING_4)
        CurrentState <= INFOPARSING;
      else if (operation == OptionsParser_op_s_DONE_21)
        CurrentState <= READY;
      else if (operation == OptionsParser_op_s_READY_1 || operation == OptionsParser_op_s_STARTPARSING_7)
        CurrentState <= STARTPARSING;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      counter <= 0;
    else begin
      if (operation == OptionsParser_op_s_DATAPARSING_14 || operation == OptionsParser_op_s_DATAPARSING_16 || operation == OptionsParser_op_s_DATAPARSING_19 || operation == OptionsParser_op_s_INFOPARSING_11 || operation == OptionsParser_op_s_INFOPARSING_12 || operation == OptionsParser_op_s_INFOPARSING_13 || operation == OptionsParser_op_s_STARTPARSING_5 || operation == OptionsParser_op_s_STARTPARSING_6 || operation == OptionsParser_op_s_STARTPARSING_7)
        counter <= (1 + counter);
      else if (operation == OptionsParser_op_s_INFOPARSING_8)
        counter <= (1 + (1 + counter));
      else if (operation == OptionsParser_op_s_READY_1)
        counter <= 0;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      fields[0] <= 0;
    else begin
      if (operation == OptionsParser_op_s_READY_1)
        fields[0] <= fieldsIn_sig[0];
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      fields[1] <= 0;
    else begin
      if (operation == OptionsParser_op_s_READY_1)
        fields[1] <= fieldsIn_sig[1];
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      fields[10] <= 0;
    else begin
      if (operation == OptionsParser_op_s_READY_1)
        fields[10] <= fieldsIn_sig[10];
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      fields[11] <= 0;
    else begin
      if (operation == OptionsParser_op_s_READY_1)
        fields[11] <= fieldsIn_sig[11];
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      fields[12] <= 0;
    else begin
      if (operation == OptionsParser_op_s_READY_1)
        fields[12] <= fieldsIn_sig[12];
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      fields[13] <= 0;
    else begin
      if (operation == OptionsParser_op_s_READY_1)
        fields[13] <= fieldsIn_sig[13];
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      fields[14] <= 0;
    else begin
      if (operation == OptionsParser_op_s_READY_1)
        fields[14] <= fieldsIn_sig[14];
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      fields[2] <= 0;
    else begin
      if (operation == OptionsParser_op_s_READY_1)
        fields[2] <= fieldsIn_sig[2];
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      fields[3] <= 0;
    else begin
      if (operation == OptionsParser_op_s_READY_1)
        fields[3] <= fieldsIn_sig[3];
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      fields[4] <= 0;
    else begin
      if (operation == OptionsParser_op_s_READY_1)
        fields[4] <= fieldsIn_sig[4];
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      fields[5] <= 0;
    else begin
      if (operation == OptionsParser_op_s_READY_1)
        fields[5] <= fieldsIn_sig[5];
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      fields[6] <= 0;
    else begin
      if (operation == OptionsParser_op_s_READY_1)
        fields[6] <= fieldsIn_sig[6];
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      fields[7] <= 0;
    else begin
      if (operation == OptionsParser_op_s_READY_1)
        fields[7] <= fieldsIn_sig[7];
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      fields[8] <= 0;
    else begin
      if (operation == OptionsParser_op_s_READY_1)
        fields[8] <= fieldsIn_sig[8];
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      fields[9] <= 0;
    else begin
      if (operation == OptionsParser_op_s_READY_1)
        fields[9] <= fieldsIn_sig[9];
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      parsed.dataOptionContents[0].contents <= 0;
    else begin
      if (operation == OptionsParser_op_s_DATAPARSING_16)
        parsed.dataOptionContents[0].contents <= ((((counter - parsed.dataOptionLen.position) - 1) == 0) ? ((counter == 0) ? fields[0] : ((counter == 1) ? fields[1] : ((counter == 2) ? fields[2] : ((counter == 3) ? fields[3] : ((counter == 4) ? fields[4] : ((counter == 5) ? fields[5] : ((counter == 6) ? fields[6] : ((counter == 7) ? fields[7] : ((counter == 8) ? fields[8] : ((counter == 9) ? fields[9] : ((counter == 10) ? fields[10] : ((counter == 11) ? fields[11] : ((counter == 12) ? fields[12] : ((counter == 13) ? fields[13] : fields[14])))))))))))))) : parsed.dataOptionContents[0].contents);
      else if (operation == OptionsParser_op_s_READY_1)
        parsed.dataOptionContents[0].contents <= 0;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      parsed.dataOptionContents[0].optiontype <= START;
    else begin
      if (operation == OptionsParser_op_s_DATAPARSING_16)
        parsed.dataOptionContents[0].optiontype <= ((counter == (1 + parsed.dataOptionLen.position)) ? DATACONTENTS : parsed.dataOptionContents[0].optiontype);
      else if (operation == OptionsParser_op_s_READY_1)
        parsed.dataOptionContents[0].optiontype <= START;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      parsed.dataOptionContents[0].position <= 0;
    else begin
      if (operation == OptionsParser_op_s_DATAPARSING_16)
        parsed.dataOptionContents[0].position <= ((counter == (1 + parsed.dataOptionLen.position)) ? counter : parsed.dataOptionContents[0].position);
      else if (operation == OptionsParser_op_s_READY_1)
        parsed.dataOptionContents[0].position <= 0;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      parsed.dataOptionContents[1].contents <= 0;
    else begin
      if (operation == OptionsParser_op_s_DATAPARSING_16)
        parsed.dataOptionContents[1].contents <= ((((counter - parsed.dataOptionLen.position) - 1) == 1) ? ((counter == 0) ? fields[0] : ((counter == 1) ? fields[1] : ((counter == 2) ? fields[2] : ((counter == 3) ? fields[3] : ((counter == 4) ? fields[4] : ((counter == 5) ? fields[5] : ((counter == 6) ? fields[6] : ((counter == 7) ? fields[7] : ((counter == 8) ? fields[8] : ((counter == 9) ? fields[9] : ((counter == 10) ? fields[10] : ((counter == 11) ? fields[11] : ((counter == 12) ? fields[12] : ((counter == 13) ? fields[13] : fields[14])))))))))))))) : parsed.dataOptionContents[1].contents);
      else if (operation == OptionsParser_op_s_READY_1)
        parsed.dataOptionContents[1].contents <= 0;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      parsed.dataOptionContents[1].optiontype <= START;
    else begin
      if (operation == OptionsParser_op_s_DATAPARSING_16)
        parsed.dataOptionContents[1].optiontype <= ((counter == (2 + parsed.dataOptionLen.position)) ? DATACONTENTS : parsed.dataOptionContents[1].optiontype);
      else if (operation == OptionsParser_op_s_READY_1)
        parsed.dataOptionContents[1].optiontype <= START;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      parsed.dataOptionContents[1].position <= 0;
    else begin
      if (operation == OptionsParser_op_s_DATAPARSING_16)
        parsed.dataOptionContents[1].position <= ((counter == (2 + parsed.dataOptionLen.position)) ? counter : parsed.dataOptionContents[1].position);
      else if (operation == OptionsParser_op_s_READY_1)
        parsed.dataOptionContents[1].position <= 0;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      parsed.dataOptionContents[2].contents <= 0;
    else begin
      if (operation == OptionsParser_op_s_DATAPARSING_16)
        parsed.dataOptionContents[2].contents <= ((((counter - parsed.dataOptionLen.position) - 1) == 2) ? ((counter == 0) ? fields[0] : ((counter == 1) ? fields[1] : ((counter == 2) ? fields[2] : ((counter == 3) ? fields[3] : ((counter == 4) ? fields[4] : ((counter == 5) ? fields[5] : ((counter == 6) ? fields[6] : ((counter == 7) ? fields[7] : ((counter == 8) ? fields[8] : ((counter == 9) ? fields[9] : ((counter == 10) ? fields[10] : ((counter == 11) ? fields[11] : ((counter == 12) ? fields[12] : ((counter == 13) ? fields[13] : fields[14])))))))))))))) : parsed.dataOptionContents[2].contents);
      else if (operation == OptionsParser_op_s_READY_1)
        parsed.dataOptionContents[2].contents <= 0;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      parsed.dataOptionContents[2].optiontype <= START;
    else begin
      if (operation == OptionsParser_op_s_DATAPARSING_16)
        parsed.dataOptionContents[2].optiontype <= ((counter == (3 + parsed.dataOptionLen.position)) ? DATACONTENTS : parsed.dataOptionContents[2].optiontype);
      else if (operation == OptionsParser_op_s_READY_1)
        parsed.dataOptionContents[2].optiontype <= START;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      parsed.dataOptionContents[2].position <= 0;
    else begin
      if (operation == OptionsParser_op_s_DATAPARSING_16)
        parsed.dataOptionContents[2].position <= ((counter == (3 + parsed.dataOptionLen.position)) ? counter : parsed.dataOptionContents[2].position);
      else if (operation == OptionsParser_op_s_READY_1)
        parsed.dataOptionContents[2].position <= 0;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      parsed.dataOptionContents[3].contents <= 0;
    else begin
      if (operation == OptionsParser_op_s_DATAPARSING_16)
        parsed.dataOptionContents[3].contents <= ((((counter - parsed.dataOptionLen.position) - 1) == 3) ? ((counter == 0) ? fields[0] : ((counter == 1) ? fields[1] : ((counter == 2) ? fields[2] : ((counter == 3) ? fields[3] : ((counter == 4) ? fields[4] : ((counter == 5) ? fields[5] : ((counter == 6) ? fields[6] : ((counter == 7) ? fields[7] : ((counter == 8) ? fields[8] : ((counter == 9) ? fields[9] : ((counter == 10) ? fields[10] : ((counter == 11) ? fields[11] : ((counter == 12) ? fields[12] : ((counter == 13) ? fields[13] : fields[14])))))))))))))) : parsed.dataOptionContents[3].contents);
      else if (operation == OptionsParser_op_s_READY_1)
        parsed.dataOptionContents[3].contents <= 0;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      parsed.dataOptionContents[3].optiontype <= START;
    else begin
      if (operation == OptionsParser_op_s_DATAPARSING_16)
        parsed.dataOptionContents[3].optiontype <= ((counter == (4 + parsed.dataOptionLen.position)) ? DATACONTENTS : parsed.dataOptionContents[3].optiontype);
      else if (operation == OptionsParser_op_s_READY_1)
        parsed.dataOptionContents[3].optiontype <= START;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      parsed.dataOptionContents[3].position <= 0;
    else begin
      if (operation == OptionsParser_op_s_DATAPARSING_16)
        parsed.dataOptionContents[3].position <= ((counter == (4 + parsed.dataOptionLen.position)) ? counter : parsed.dataOptionContents[3].position);
      else if (operation == OptionsParser_op_s_READY_1)
        parsed.dataOptionContents[3].position <= 0;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      parsed.dataOptionContents[4].contents <= 0;
    else begin
      if (operation == OptionsParser_op_s_DATAPARSING_16)
        parsed.dataOptionContents[4].contents <= ((((counter - parsed.dataOptionLen.position) - 1) == 4) ? ((counter == 0) ? fields[0] : ((counter == 1) ? fields[1] : ((counter == 2) ? fields[2] : ((counter == 3) ? fields[3] : ((counter == 4) ? fields[4] : ((counter == 5) ? fields[5] : ((counter == 6) ? fields[6] : ((counter == 7) ? fields[7] : ((counter == 8) ? fields[8] : ((counter == 9) ? fields[9] : ((counter == 10) ? fields[10] : ((counter == 11) ? fields[11] : ((counter == 12) ? fields[12] : ((counter == 13) ? fields[13] : fields[14])))))))))))))) : parsed.dataOptionContents[4].contents);
      else if (operation == OptionsParser_op_s_READY_1)
        parsed.dataOptionContents[4].contents <= 0;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      parsed.dataOptionContents[4].optiontype <= START;
    else begin
      if (operation == OptionsParser_op_s_DATAPARSING_16)
        parsed.dataOptionContents[4].optiontype <= ((counter == (5 + parsed.dataOptionLen.position)) ? DATACONTENTS : parsed.dataOptionContents[4].optiontype);
      else if (operation == OptionsParser_op_s_READY_1)
        parsed.dataOptionContents[4].optiontype <= START;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      parsed.dataOptionContents[4].position <= 0;
    else begin
      if (operation == OptionsParser_op_s_DATAPARSING_16)
        parsed.dataOptionContents[4].position <= ((counter == (5 + parsed.dataOptionLen.position)) ? counter : parsed.dataOptionContents[4].position);
      else if (operation == OptionsParser_op_s_READY_1)
        parsed.dataOptionContents[4].position <= 0;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      parsed.dataOptionLen.contents <= 0;
    else begin
      if (operation == OptionsParser_op_s_DATAPARSING_14)
        parsed.dataOptionLen.contents <= ((counter == 0) ? fields[0] : ((counter == 1) ? fields[1] : ((counter == 2) ? fields[2] : ((counter == 3) ? fields[3] : ((counter == 4) ? fields[4] : ((counter == 5) ? fields[5] : ((counter == 6) ? fields[6] : ((counter == 7) ? fields[7] : ((counter == 8) ? fields[8] : ((counter == 9) ? fields[9] : ((counter == 10) ? fields[10] : ((counter == 11) ? fields[11] : ((counter == 12) ? fields[12] : ((counter == 13) ? fields[13] : fields[14]))))))))))))));
      else if (operation == OptionsParser_op_s_READY_1)
        parsed.dataOptionLen.contents <= 0;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      parsed.dataOptionLen.optiontype <= START;
    else begin
      if (operation == OptionsParser_op_s_DATAPARSING_14)
        parsed.dataOptionLen.optiontype <= DATALEN;
      else if (operation == OptionsParser_op_s_READY_1)
        parsed.dataOptionLen.optiontype <= START;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      parsed.dataOptionLen.position <= 0;
    else begin
      if (operation == OptionsParser_op_s_DATAPARSING_14)
        parsed.dataOptionLen.position <= counter;
      else if (operation == OptionsParser_op_s_READY_1)
        parsed.dataOptionLen.position <= 0;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      parsed.dataOption.contents <= 0;
    else begin
      if (operation == OptionsParser_op_s_DATAPARSING_14)
        parsed.dataOption.contents <= 4;
      else if (operation == OptionsParser_op_s_READY_1)
        parsed.dataOption.contents <= 0;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      parsed.dataOption.optiontype <= START;
    else begin
      if (operation == OptionsParser_op_s_DATAPARSING_14)
        parsed.dataOption.optiontype <= DATA;
      else if (operation == OptionsParser_op_s_READY_1)
        parsed.dataOption.optiontype <= START;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      parsed.dataOption.position <= 0;
    else begin
      if (operation == OptionsParser_op_s_DATAPARSING_14)
        parsed.dataOption.position <= (4294967295 + counter);
      else if (operation == OptionsParser_op_s_READY_1)
        parsed.dataOption.position <= 0;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      parsed.endOption.contents <= 0;
    else begin
      if (operation == OptionsParser_op_s_ENDPARSING_20)
        parsed.endOption.contents <= 2;
      else if (operation == OptionsParser_op_s_READY_1)
        parsed.endOption.contents <= 0;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      parsed.endOption.optiontype <= START;
    else begin
      if (operation == OptionsParser_op_s_ENDPARSING_20)
        parsed.endOption.optiontype <= ENDOPTION;
      else if (operation == OptionsParser_op_s_READY_1)
        parsed.endOption.optiontype <= START;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      parsed.endOption.position <= 0;
    else begin
      if (operation == OptionsParser_op_s_ENDPARSING_20)
        parsed.endOption.position <= counter;
      else if (operation == OptionsParser_op_s_READY_1)
        parsed.endOption.position <= 0;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      parsed.hasData <= 0;
    else begin
      if (operation == OptionsParser_op_s_DATAPARSING_14)
        parsed.hasData <= 1;
      else if (operation == OptionsParser_op_s_READY_1)
        parsed.hasData <= 0;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      parsed.hasEnd <= 0;
    else begin
      if (operation == OptionsParser_op_s_ENDPARSING_20)
        parsed.hasEnd <= 1;
      else if (operation == OptionsParser_op_s_READY_1)
        parsed.hasEnd <= 0;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      parsed.hasError <= 0;
    else begin
      if (operation == OptionsParser_op_s_DATAPARSING_15 || operation == OptionsParser_op_s_INFOPARSING_11 || operation == OptionsParser_op_s_INFOPARSING_9 || operation == OptionsParser_op_s_STARTPARSING_5)
        parsed.hasError <= 1;
      else if (operation == OptionsParser_op_s_ENDPARSING_20)
        parsed.hasError <= (!(parsed.hasStart) || parsed.hasError);
      else if (operation == OptionsParser_op_s_READY_1 || operation == OptionsParser_op_s_STARTPARSING_6 || operation == OptionsParser_op_s_STARTPARSING_3 || operation == OptionsParser_op_s_STARTPARSING_4 || operation == OptionsParser_op_s_STARTPARSING_7)
        parsed.hasError <= 0;
      else if (operation == OptionsParser_op_s_STARTPARSING_2)
        parsed.hasError <= (((counter > 14) && parsed.hasStart) ? 1 : 0);
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      parsed.hasInfo <= 0;
    else begin
      if (operation == OptionsParser_op_s_INFOPARSING_8)
        parsed.hasInfo <= 1;
      else if (operation == OptionsParser_op_s_READY_1)
        parsed.hasInfo <= 0;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      parsed.hasStart <= 0;
    else begin
      if (operation == OptionsParser_op_s_READY_1)
        parsed.hasStart <= 0;
      else if (operation == OptionsParser_op_s_STARTPARSING_7)
        parsed.hasStart <= (((((counter == 0) ? fields[0] : ((counter == 1) ? fields[1] : ((counter == 2) ? fields[2] : ((counter == 3) ? fields[3] : ((counter == 4) ? fields[4] : ((counter == 5) ? fields[5] : ((counter == 6) ? fields[6] : ((counter == 7) ? fields[7] : ((counter == 8) ? fields[8] : ((counter == 9) ? fields[9] : ((counter == 10) ? fields[10] : ((counter == 11) ? fields[11] : ((counter == 12) ? fields[12] : ((counter == 13) ? fields[13] : fields[14])))))))))))))) == 1) && (counter < 15)) ? 1 : parsed.hasStart);
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      parsed.infoOptionContents.contents <= 0;
    else begin
      if (operation == OptionsParser_op_s_INFOPARSING_8)
        parsed.infoOptionContents.contents <= (((counter + 1) == 0) ? fields[0] : (((counter + 1) == 1) ? fields[1] : (((counter + 1) == 2) ? fields[2] : (((counter + 1) == 3) ? fields[3] : (((counter + 1) == 4) ? fields[4] : (((counter + 1) == 5) ? fields[5] : (((counter + 1) == 6) ? fields[6] : (((counter + 1) == 7) ? fields[7] : (((counter + 1) == 8) ? fields[8] : (((counter + 1) == 9) ? fields[9] : (((counter + 1) == 10) ? fields[10] : (((counter + 1) == 11) ? fields[11] : (((counter + 1) == 12) ? fields[12] : (((counter + 1) == 13) ? fields[13] : fields[14]))))))))))))));
      else if (operation == OptionsParser_op_s_READY_1)
        parsed.infoOptionContents.contents <= 0;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      parsed.infoOptionContents.optiontype <= START;
    else begin
      if (operation == OptionsParser_op_s_INFOPARSING_8)
        parsed.infoOptionContents.optiontype <= INFOCONTENTS;
      else if (operation == OptionsParser_op_s_READY_1)
        parsed.infoOptionContents.optiontype <= START;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      parsed.infoOptionContents.position <= 0;
    else begin
      if (operation == OptionsParser_op_s_INFOPARSING_8)
        parsed.infoOptionContents.position <= (1 + counter);
      else if (operation == OptionsParser_op_s_READY_1)
        parsed.infoOptionContents.position <= 0;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      parsed.infoOption.contents <= 0;
    else begin
      if (operation == OptionsParser_op_s_INFOPARSING_8)
        parsed.infoOption.contents <= 3;
      else if (operation == OptionsParser_op_s_READY_1)
        parsed.infoOption.contents <= 0;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      parsed.infoOption.optiontype <= START;
    else begin
      if (operation == OptionsParser_op_s_INFOPARSING_8)
        parsed.infoOption.optiontype <= INFO;
      else if (operation == OptionsParser_op_s_READY_1)
        parsed.infoOption.optiontype <= START;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      parsed.infoOption.position <= 0;
    else begin
      if (operation == OptionsParser_op_s_INFOPARSING_8)
        parsed.infoOption.position <= counter;
      else if (operation == OptionsParser_op_s_READY_1)
        parsed.infoOption.position <= 0;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      parsed.startOption.contents <= 0;
    else begin
      if (operation == OptionsParser_op_s_READY_1)
        parsed.startOption.contents <= 0;
      else if (operation == OptionsParser_op_s_STARTPARSING_5 || operation == OptionsParser_op_s_STARTPARSING_6 || operation == OptionsParser_op_s_STARTPARSING_3 || operation == OptionsParser_op_s_STARTPARSING_4)
        parsed.startOption.contents <= 1;
      else if (operation == OptionsParser_op_s_STARTPARSING_2)
        parsed.startOption.contents <= (parsed.hasStart ? 1 : parsed.startOption.contents);
      else if (operation == OptionsParser_op_s_STARTPARSING_7)
        parsed.startOption.contents <= ((((((counter == 0) ? fields[0] : ((counter == 1) ? fields[1] : ((counter == 2) ? fields[2] : ((counter == 3) ? fields[3] : ((counter == 4) ? fields[4] : ((counter == 5) ? fields[5] : ((counter == 6) ? fields[6] : ((counter == 7) ? fields[7] : ((counter == 8) ? fields[8] : ((counter == 9) ? fields[9] : ((counter == 10) ? fields[10] : ((counter == 11) ? fields[11] : ((counter == 12) ? fields[12] : ((counter == 13) ? fields[13] : fields[14])))))))))))))) == 1) && (counter < 15)) ? 1 : parsed.hasStart) ? 1 : parsed.startOption.contents);
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      parsed.startOption.optiontype <= START;
    else begin
      if (operation == OptionsParser_op_s_READY_1 || operation == OptionsParser_op_s_STARTPARSING_5 || operation == OptionsParser_op_s_STARTPARSING_6 || operation == OptionsParser_op_s_STARTPARSING_3 || operation == OptionsParser_op_s_STARTPARSING_4)
        parsed.startOption.optiontype <= START;
      else if (operation == OptionsParser_op_s_STARTPARSING_2)
        parsed.startOption.optiontype <= (parsed.hasStart ? START : parsed.startOption.optiontype);
      else if (operation == OptionsParser_op_s_STARTPARSING_7)
        parsed.startOption.optiontype <= ((((((counter == 0) ? fields[0] : ((counter == 1) ? fields[1] : ((counter == 2) ? fields[2] : ((counter == 3) ? fields[3] : ((counter == 4) ? fields[4] : ((counter == 5) ? fields[5] : ((counter == 6) ? fields[6] : ((counter == 7) ? fields[7] : ((counter == 8) ? fields[8] : ((counter == 9) ? fields[9] : ((counter == 10) ? fields[10] : ((counter == 11) ? fields[11] : ((counter == 12) ? fields[12] : ((counter == 13) ? fields[13] : fields[14])))))))))))))) == 1) && (counter < 15)) ? 1 : parsed.hasStart) ? START : parsed.startOption.optiontype);
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      parsed.startOption.position <= 0;
    else begin
      if (operation == OptionsParser_op_s_READY_1)
        parsed.startOption.position <= 0;
      else if (operation == OptionsParser_op_s_STARTPARSING_7)
        parsed.startOption.position <= (((((counter == 0) ? fields[0] : ((counter == 1) ? fields[1] : ((counter == 2) ? fields[2] : ((counter == 3) ? fields[3] : ((counter == 4) ? fields[4] : ((counter == 5) ? fields[5] : ((counter == 6) ? fields[6] : ((counter == 7) ? fields[7] : ((counter == 8) ? fields[8] : ((counter == 9) ? fields[9] : ((counter == 10) ? fields[10] : ((counter == 11) ? fields[11] : ((counter == 12) ? fields[12] : ((counter == 13) ? fields[13] : fields[14])))))))))))))) == 1) && (counter < 15)) ? counter : parsed.startOption.position);
    end
  end

  always_ff @(posedge clk) begin
    if (operation == OptionsParser_op_s_DATAPARSING_15 || operation == OptionsParser_op_s_ENDPARSING_20 || operation == OptionsParser_op_s_INFOPARSING_9 || operation == OptionsParser_op_s_STARTPARSING_2)
      parsedOut_sig.dataOptionContents[0].contents <= parsed.dataOptionContents[0].contents;
  end

  always_ff @(posedge clk) begin
    if (operation == OptionsParser_op_s_DATAPARSING_15 || operation == OptionsParser_op_s_ENDPARSING_20 || operation == OptionsParser_op_s_INFOPARSING_9 || operation == OptionsParser_op_s_STARTPARSING_2)
      parsedOut_sig.dataOptionContents[0].optiontype <= parsed.dataOptionContents[0].optiontype;
  end

  always_ff @(posedge clk) begin
    if (operation == OptionsParser_op_s_DATAPARSING_15 || operation == OptionsParser_op_s_ENDPARSING_20 || operation == OptionsParser_op_s_INFOPARSING_9 || operation == OptionsParser_op_s_STARTPARSING_2)
      parsedOut_sig.dataOptionContents[0].position <= parsed.dataOptionContents[0].position;
  end

  always_ff @(posedge clk) begin
    if (operation == OptionsParser_op_s_DATAPARSING_15 || operation == OptionsParser_op_s_ENDPARSING_20 || operation == OptionsParser_op_s_INFOPARSING_9 || operation == OptionsParser_op_s_STARTPARSING_2)
      parsedOut_sig.dataOptionContents[1].contents <= parsed.dataOptionContents[1].contents;
  end

  always_ff @(posedge clk) begin
    if (operation == OptionsParser_op_s_DATAPARSING_15 || operation == OptionsParser_op_s_ENDPARSING_20 || operation == OptionsParser_op_s_INFOPARSING_9 || operation == OptionsParser_op_s_STARTPARSING_2)
      parsedOut_sig.dataOptionContents[1].optiontype <= parsed.dataOptionContents[1].optiontype;
  end

  always_ff @(posedge clk) begin
    if (operation == OptionsParser_op_s_DATAPARSING_15 || operation == OptionsParser_op_s_ENDPARSING_20 || operation == OptionsParser_op_s_INFOPARSING_9 || operation == OptionsParser_op_s_STARTPARSING_2)
      parsedOut_sig.dataOptionContents[1].position <= parsed.dataOptionContents[1].position;
  end

  always_ff @(posedge clk) begin
    if (operation == OptionsParser_op_s_DATAPARSING_15 || operation == OptionsParser_op_s_ENDPARSING_20 || operation == OptionsParser_op_s_INFOPARSING_9 || operation == OptionsParser_op_s_STARTPARSING_2)
      parsedOut_sig.dataOptionContents[2].contents <= parsed.dataOptionContents[2].contents;
  end

  always_ff @(posedge clk) begin
    if (operation == OptionsParser_op_s_DATAPARSING_15 || operation == OptionsParser_op_s_ENDPARSING_20 || operation == OptionsParser_op_s_INFOPARSING_9 || operation == OptionsParser_op_s_STARTPARSING_2)
      parsedOut_sig.dataOptionContents[2].optiontype <= parsed.dataOptionContents[2].optiontype;
  end

  always_ff @(posedge clk) begin
    if (operation == OptionsParser_op_s_DATAPARSING_15 || operation == OptionsParser_op_s_ENDPARSING_20 || operation == OptionsParser_op_s_INFOPARSING_9 || operation == OptionsParser_op_s_STARTPARSING_2)
      parsedOut_sig.dataOptionContents[2].position <= parsed.dataOptionContents[2].position;
  end

  always_ff @(posedge clk) begin
    if (operation == OptionsParser_op_s_DATAPARSING_15 || operation == OptionsParser_op_s_ENDPARSING_20 || operation == OptionsParser_op_s_INFOPARSING_9 || operation == OptionsParser_op_s_STARTPARSING_2)
      parsedOut_sig.dataOptionContents[3].contents <= parsed.dataOptionContents[3].contents;
  end

  always_ff @(posedge clk) begin
    if (operation == OptionsParser_op_s_DATAPARSING_15 || operation == OptionsParser_op_s_ENDPARSING_20 || operation == OptionsParser_op_s_INFOPARSING_9 || operation == OptionsParser_op_s_STARTPARSING_2)
      parsedOut_sig.dataOptionContents[3].optiontype <= parsed.dataOptionContents[3].optiontype;
  end

  always_ff @(posedge clk) begin
    if (operation == OptionsParser_op_s_DATAPARSING_15 || operation == OptionsParser_op_s_ENDPARSING_20 || operation == OptionsParser_op_s_INFOPARSING_9 || operation == OptionsParser_op_s_STARTPARSING_2)
      parsedOut_sig.dataOptionContents[3].position <= parsed.dataOptionContents[3].position;
  end

  always_ff @(posedge clk) begin
    if (operation == OptionsParser_op_s_DATAPARSING_15 || operation == OptionsParser_op_s_ENDPARSING_20 || operation == OptionsParser_op_s_INFOPARSING_9 || operation == OptionsParser_op_s_STARTPARSING_2)
      parsedOut_sig.dataOptionContents[4].contents <= parsed.dataOptionContents[4].contents;
  end

  always_ff @(posedge clk) begin
    if (operation == OptionsParser_op_s_DATAPARSING_15 || operation == OptionsParser_op_s_ENDPARSING_20 || operation == OptionsParser_op_s_INFOPARSING_9 || operation == OptionsParser_op_s_STARTPARSING_2)
      parsedOut_sig.dataOptionContents[4].optiontype <= parsed.dataOptionContents[4].optiontype;
  end

  always_ff @(posedge clk) begin
    if (operation == OptionsParser_op_s_DATAPARSING_15 || operation == OptionsParser_op_s_ENDPARSING_20 || operation == OptionsParser_op_s_INFOPARSING_9 || operation == OptionsParser_op_s_STARTPARSING_2)
      parsedOut_sig.dataOptionContents[4].position <= parsed.dataOptionContents[4].position;
  end

  always_ff @(posedge clk) begin
    if (operation == OptionsParser_op_s_DATAPARSING_15 || operation == OptionsParser_op_s_ENDPARSING_20 || operation == OptionsParser_op_s_INFOPARSING_9 || operation == OptionsParser_op_s_STARTPARSING_2)
      parsedOut_sig.dataOptionLen.contents <= parsed.dataOptionLen.contents;
  end

  always_ff @(posedge clk) begin
    if (operation == OptionsParser_op_s_DATAPARSING_15 || operation == OptionsParser_op_s_ENDPARSING_20 || operation == OptionsParser_op_s_INFOPARSING_9 || operation == OptionsParser_op_s_STARTPARSING_2)
      parsedOut_sig.dataOptionLen.optiontype <= parsed.dataOptionLen.optiontype;
  end

  always_ff @(posedge clk) begin
    if (operation == OptionsParser_op_s_DATAPARSING_15 || operation == OptionsParser_op_s_ENDPARSING_20 || operation == OptionsParser_op_s_INFOPARSING_9 || operation == OptionsParser_op_s_STARTPARSING_2)
      parsedOut_sig.dataOptionLen.position <= parsed.dataOptionLen.position;
  end

  always_ff @(posedge clk) begin
    if (operation == OptionsParser_op_s_DATAPARSING_15 || operation == OptionsParser_op_s_ENDPARSING_20 || operation == OptionsParser_op_s_INFOPARSING_9 || operation == OptionsParser_op_s_STARTPARSING_2)
      parsedOut_sig.dataOption.contents <= parsed.dataOption.contents;
  end

  always_ff @(posedge clk) begin
    if (operation == OptionsParser_op_s_DATAPARSING_15 || operation == OptionsParser_op_s_ENDPARSING_20 || operation == OptionsParser_op_s_INFOPARSING_9 || operation == OptionsParser_op_s_STARTPARSING_2)
      parsedOut_sig.dataOption.optiontype <= parsed.dataOption.optiontype;
  end

  always_ff @(posedge clk) begin
    if (operation == OptionsParser_op_s_DATAPARSING_15 || operation == OptionsParser_op_s_ENDPARSING_20 || operation == OptionsParser_op_s_INFOPARSING_9 || operation == OptionsParser_op_s_STARTPARSING_2)
      parsedOut_sig.dataOption.position <= parsed.dataOption.position;
  end

  always_ff @(posedge clk) begin
    if (operation == OptionsParser_op_s_DATAPARSING_15 || operation == OptionsParser_op_s_INFOPARSING_9 || operation == OptionsParser_op_s_STARTPARSING_2)
      parsedOut_sig.endOption.contents <= parsed.endOption.contents;
    else if (operation == OptionsParser_op_s_ENDPARSING_20)
      parsedOut_sig.endOption.contents <= 2;
  end

  always_ff @(posedge clk) begin
    if (operation == OptionsParser_op_s_DATAPARSING_15 || operation == OptionsParser_op_s_INFOPARSING_9 || operation == OptionsParser_op_s_STARTPARSING_2)
      parsedOut_sig.endOption.optiontype <= parsed.endOption.optiontype;
    else if (operation == OptionsParser_op_s_ENDPARSING_20)
      parsedOut_sig.endOption.optiontype <= ENDOPTION;
  end

  always_ff @(posedge clk) begin
    if (operation == OptionsParser_op_s_DATAPARSING_15 || operation == OptionsParser_op_s_INFOPARSING_9 || operation == OptionsParser_op_s_STARTPARSING_2)
      parsedOut_sig.endOption.position <= parsed.endOption.position;
    else if (operation == OptionsParser_op_s_ENDPARSING_20)
      parsedOut_sig.endOption.position <= counter;
  end

  always_ff @(posedge clk) begin
    if (operation == OptionsParser_op_s_DATAPARSING_15 || operation == OptionsParser_op_s_ENDPARSING_20 || operation == OptionsParser_op_s_INFOPARSING_9 || operation == OptionsParser_op_s_STARTPARSING_2)
      parsedOut_sig.hasData <= parsed.hasData;
  end

  always_ff @(posedge clk) begin
    if (operation == OptionsParser_op_s_DATAPARSING_15 || operation == OptionsParser_op_s_INFOPARSING_9 || operation == OptionsParser_op_s_STARTPARSING_2)
      parsedOut_sig.hasEnd <= parsed.hasEnd;
    else if (operation == OptionsParser_op_s_ENDPARSING_20)
      parsedOut_sig.hasEnd <= 1;
  end

  always_ff @(posedge clk) begin
    if (operation == OptionsParser_op_s_DATAPARSING_15 || operation == OptionsParser_op_s_INFOPARSING_9)
      parsedOut_sig.hasError <= 1;
    else if (operation == OptionsParser_op_s_ENDPARSING_20)
      parsedOut_sig.hasError <= (!(parsed.hasStart) || parsed.hasError);
    else if (operation == OptionsParser_op_s_STARTPARSING_2)
      parsedOut_sig.hasError <= (((counter > 14) && parsed.hasStart) ? 1 : 0);
  end

  always_ff @(posedge clk) begin
    if (operation == OptionsParser_op_s_DATAPARSING_15 || operation == OptionsParser_op_s_ENDPARSING_20 || operation == OptionsParser_op_s_INFOPARSING_9 || operation == OptionsParser_op_s_STARTPARSING_2)
      parsedOut_sig.hasInfo <= parsed.hasInfo;
  end

  always_ff @(posedge clk) begin
    if (operation == OptionsParser_op_s_DATAPARSING_15 || operation == OptionsParser_op_s_ENDPARSING_20 || operation == OptionsParser_op_s_INFOPARSING_9 || operation == OptionsParser_op_s_STARTPARSING_2)
      parsedOut_sig.hasStart <= parsed.hasStart;
  end

  always_ff @(posedge clk) begin
    if (operation == OptionsParser_op_s_DATAPARSING_15 || operation == OptionsParser_op_s_ENDPARSING_20 || operation == OptionsParser_op_s_INFOPARSING_9 || operation == OptionsParser_op_s_STARTPARSING_2)
      parsedOut_sig.infoOptionContents.contents <= parsed.infoOptionContents.contents;
  end

  always_ff @(posedge clk) begin
    if (operation == OptionsParser_op_s_DATAPARSING_15 || operation == OptionsParser_op_s_ENDPARSING_20 || operation == OptionsParser_op_s_INFOPARSING_9 || operation == OptionsParser_op_s_STARTPARSING_2)
      parsedOut_sig.infoOptionContents.optiontype <= parsed.infoOptionContents.optiontype;
  end

  always_ff @(posedge clk) begin
    if (operation == OptionsParser_op_s_DATAPARSING_15 || operation == OptionsParser_op_s_ENDPARSING_20 || operation == OptionsParser_op_s_INFOPARSING_9 || operation == OptionsParser_op_s_STARTPARSING_2)
      parsedOut_sig.infoOptionContents.position <= parsed.infoOptionContents.position;
  end

  always_ff @(posedge clk) begin
    if (operation == OptionsParser_op_s_DATAPARSING_15 || operation == OptionsParser_op_s_ENDPARSING_20 || operation == OptionsParser_op_s_INFOPARSING_9 || operation == OptionsParser_op_s_STARTPARSING_2)
      parsedOut_sig.infoOption.contents <= parsed.infoOption.contents;
  end

  always_ff @(posedge clk) begin
    if (operation == OptionsParser_op_s_DATAPARSING_15 || operation == OptionsParser_op_s_ENDPARSING_20 || operation == OptionsParser_op_s_INFOPARSING_9 || operation == OptionsParser_op_s_STARTPARSING_2)
      parsedOut_sig.infoOption.optiontype <= parsed.infoOption.optiontype;
  end

  always_ff @(posedge clk) begin
    if (operation == OptionsParser_op_s_DATAPARSING_15 || operation == OptionsParser_op_s_ENDPARSING_20 || operation == OptionsParser_op_s_INFOPARSING_9 || operation == OptionsParser_op_s_STARTPARSING_2)
      parsedOut_sig.infoOption.position <= parsed.infoOption.position;
  end

  always_ff @(posedge clk) begin
    if (operation == OptionsParser_op_s_DATAPARSING_15 || operation == OptionsParser_op_s_INFOPARSING_9)
      parsedOut_sig.isEmpty <= (((!((parsed.hasData || parsed.hasInfo)) && parsed.hasStart) && parsed.hasEnd) || !((((parsed.hasData || parsed.hasInfo) || parsed.hasStart) || parsed.hasEnd)));
    else if (operation == OptionsParser_op_s_ENDPARSING_20)
      parsedOut_sig.isEmpty <= (!((parsed.hasData || parsed.hasInfo)) && parsed.hasStart);
    else if (operation == OptionsParser_op_s_STARTPARSING_2)
      parsedOut_sig.isEmpty <= ((((!((parsed.hasData || parsed.hasInfo)) && parsed.hasStart) && parsed.hasEnd) || !((((parsed.hasData || parsed.hasInfo) || parsed.hasStart) || parsed.hasEnd))) ? 1 : 0);
  end

  always_ff @(posedge clk) begin
    if (operation == OptionsParser_op_s_DATAPARSING_15 || operation == OptionsParser_op_s_ENDPARSING_20 || operation == OptionsParser_op_s_INFOPARSING_9)
      parsedOut_sig.startOption.contents <= parsed.startOption.contents;
    else if (operation == OptionsParser_op_s_STARTPARSING_2)
      parsedOut_sig.startOption.contents <= (parsed.hasStart ? 1 : parsed.startOption.contents);
  end

  always_ff @(posedge clk) begin
    if (operation == OptionsParser_op_s_DATAPARSING_15 || operation == OptionsParser_op_s_ENDPARSING_20 || operation == OptionsParser_op_s_INFOPARSING_9)
      parsedOut_sig.startOption.optiontype <= parsed.startOption.optiontype;
    else if (operation == OptionsParser_op_s_STARTPARSING_2)
      parsedOut_sig.startOption.optiontype <= (parsed.hasStart ? START : parsed.startOption.optiontype);
  end

  always_ff @(posedge clk) begin
    if (operation == OptionsParser_op_s_DATAPARSING_15 || operation == OptionsParser_op_s_ENDPARSING_20 || operation == OptionsParser_op_s_INFOPARSING_9 || operation == OptionsParser_op_s_STARTPARSING_2)
      parsedOut_sig.startOption.position <= parsed.startOption.position;
  end

  always_ff @(posedge clk) begin
    if (rst)
      fieldsIn_notify <= 1;
    else begin
      if (operation == OptionsParser_op_s_DATAPARSING_14 || operation == OptionsParser_op_s_DATAPARSING_16 || operation == OptionsParser_op_s_DATAPARSING_19 || operation == OptionsParser_op_s_DATAPARSING_15 || operation == OptionsParser_op_s_DATAPARSING_17 || operation == OptionsParser_op_s_DATAPARSING_18 || operation == OptionsParser_op_wait_s_DONE || operation == OptionsParser_op_s_ENDPARSING_20 || operation == OptionsParser_op_s_INFOPARSING_11 || operation == OptionsParser_op_s_INFOPARSING_12 || operation == OptionsParser_op_s_INFOPARSING_9 || operation == OptionsParser_op_s_INFOPARSING_10 || operation == OptionsParser_op_s_INFOPARSING_8 || operation == OptionsParser_op_s_INFOPARSING_13 || operation == OptionsParser_op_s_READY_1 || operation == OptionsParser_op_s_STARTPARSING_5 || operation == OptionsParser_op_s_STARTPARSING_6 || operation == OptionsParser_op_s_STARTPARSING_2 || operation == OptionsParser_op_s_STARTPARSING_3 || operation == OptionsParser_op_s_STARTPARSING_4 || operation == OptionsParser_op_s_STARTPARSING_7)
        fieldsIn_notify <= 0;
      else if (operation == OptionsParser_op_s_DONE_21 || operation == OptionsParser_op_wait_s_READY)
        fieldsIn_notify <= 1;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      parsedOut_notify <= 0;
    else begin
      if (operation == OptionsParser_op_s_DATAPARSING_14 || operation == OptionsParser_op_s_DATAPARSING_16 || operation == OptionsParser_op_s_DATAPARSING_19 || operation == OptionsParser_op_s_DATAPARSING_17 || operation == OptionsParser_op_s_DATAPARSING_18 || operation == OptionsParser_op_s_DONE_21 || operation == OptionsParser_op_s_INFOPARSING_11 || operation == OptionsParser_op_s_INFOPARSING_12 || operation == OptionsParser_op_s_INFOPARSING_10 || operation == OptionsParser_op_s_INFOPARSING_8 || operation == OptionsParser_op_s_INFOPARSING_13 || operation == OptionsParser_op_s_READY_1 || operation == OptionsParser_op_wait_s_READY || operation == OptionsParser_op_s_STARTPARSING_5 || operation == OptionsParser_op_s_STARTPARSING_6 || operation == OptionsParser_op_s_STARTPARSING_3 || operation == OptionsParser_op_s_STARTPARSING_4 || operation == OptionsParser_op_s_STARTPARSING_7)
        parsedOut_notify <= 0;
      else if (operation == OptionsParser_op_s_DATAPARSING_15 || operation == OptionsParser_op_wait_s_DONE || operation == OptionsParser_op_s_ENDPARSING_20 || operation == OptionsParser_op_s_INFOPARSING_9 || operation == OptionsParser_op_s_STARTPARSING_2)
        parsedOut_notify <= 1;
    end
  end

  assign CurrentState_out = CurrentState;
  assign counter_out      = counter;
  assign fields_out       = fields;
  assign parsed_out       = parsed;

endmodule
