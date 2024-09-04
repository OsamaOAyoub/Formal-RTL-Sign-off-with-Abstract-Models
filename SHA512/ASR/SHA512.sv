import global_package::*;
import SHA512_operations::*;


module SHA512 (
  input  bit                  rst,
  input  bit                  clk,
  input  st_SHA_Args          SHA_Input_sig,
  input  bit                  SHA_Input_sync,
  output bit                  SHA_Input_notify,
  output bit unsigned [511:0] out_sig,
  output bit                  out_notify
);

  bit signed [31:0]   i;
  SHA512_operations_t operation;

  SHA512_control SHA512_control_inst (
    .rst           (rst),
    .clk           (clk),
    .SHA_Input_sig (SHA_Input_sig),
    .SHA_Input_sync(SHA_Input_sync),
    .i             (i),
    .operation     (operation)
  );

  SHA512_computational SHA512_computational_inst (
    .rst             (rst),
    .clk             (clk),
    .SHA_Input_sig   (SHA_Input_sig),
    .SHA_Input_notify(SHA_Input_notify),
    .out_sig         (out_sig),
    .out_notify      (out_notify),
    .i_out           (i),
    .operation       (operation)
  );

endmodule
