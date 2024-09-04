import global_package::*;
import OptionsParser_operations::*;


module OptionsParser (
  input  bit              rst,
  input  bit              clk,
  input  a_unsigned_32_15 fieldsIn_sig,
  input  bit              fieldsIn_sync,
  output bit              fieldsIn_notify,
  output st_ParsedOptions parsedOut_sig,
  input  bit              parsedOut_sync,
  output bit              parsedOut_notify
);

  e_States                   CurrentState;
  bit unsigned [31:0]        counter;
  a_unsigned_32_15           fields;
  st_ParsedOptions           parsed;
  OptionsParser_operations_t operation;

  OptionsParser_control OptionsParser_control_inst (
    .rst           (rst),
    .clk           (clk),
    .fieldsIn_sync (fieldsIn_sync),
    .parsedOut_sync(parsedOut_sync),
    .CurrentState  (CurrentState),
    .counter       (counter),
    .fields        (fields),
    .parsed        (parsed),
    .operation     (operation)
  );

  OptionsParser_computational OptionsParser_computational_inst (
    .rst             (rst),
    .clk             (clk),
    .fieldsIn_sig    (fieldsIn_sig),
    .fieldsIn_notify (fieldsIn_notify),
    .parsedOut_sig   (parsedOut_sig),
    .parsedOut_notify(parsedOut_notify),
    .CurrentState_out(CurrentState),
    .counter_out     (counter),
    .fields_out      (fields),
    .parsed_out      (parsed),
    .operation       (operation)
  );

endmodule
