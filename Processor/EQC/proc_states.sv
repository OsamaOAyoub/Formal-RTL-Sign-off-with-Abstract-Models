import global_package::*;
import proc_states_package::*;
import proc_states_operations::*;


module proc_states (
  input  bit                 rst,
  input  bit                 clk,
  output bit unsigned [7:0] dataaddr_sig,
  input  bit unsigned [7:0] datain_sig,
  output bit unsigned [7:0] dataout_sig,
  input  bit unsigned [15:0] instrIn_sig,
  output bit unsigned [15:0] instraddr_sig,
  output bit                 wen_sig
);

  bit unsigned [15:0]      instr;
  a_sc_unsigned_8_8        reg_file;
  proc_states_operations_t operation;

  proc_states_control proc_states_control_inst (
    .rst      (rst),
    .clk      (clk),
    .instr    (instr),
    .reg_file (reg_file),
    .operation(operation)
  );

  proc_states_computational proc_states_computational_inst (
    .rst          (rst),
    .clk          (clk),
    .dataaddr_sig (dataaddr_sig),
    .datain_sig   (datain_sig),
    .dataout_sig  (dataout_sig),
    .instrIn_sig  (instrIn_sig),
    .instraddr_sig(instraddr_sig),
    .wen_sig      (wen_sig),
    .instr_out    (instr),
    .reg_file_out (reg_file),
    .operation    (operation)
  );

endmodule