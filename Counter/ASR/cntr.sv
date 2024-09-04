import cntr_operations::*;


module cntr (
  input  bit                 rst,
  input  bit                 clk,
  output bit unsigned [31:0] cnt_out_sig,
  input  bit                 en_sig
);

  bit unsigned [31:0] cnt_out_t;
  cntr_operations_t   operation;

  cntr_control cntr_control_inst (
    .rst      (rst),
    .clk      (clk),
    .en_sig   (en_sig),
    .cnt_out_t(cnt_out_t),
    .operation(operation)
  );

  cntr_computational cntr_computational_inst (
    .rst          (rst),
    .clk          (clk),
    .cnt_out_sig  (cnt_out_sig),
    .en_sig       (en_sig),
    .cnt_out_t_out(cnt_out_t),
    .operation    (operation)
  );

endmodule
