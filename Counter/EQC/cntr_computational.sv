import cntr_operations::*;


module cntr_computational (
  input  bit                 rst,
  input  bit                 clk,
  output bit unsigned [31:0] cnt_out_sig,
  input  bit                 en_sig,
  output bit unsigned [31:0] cnt_out_t_out,
  input  cntr_operations_t   operation
);

  bit unsigned [31:0] cnt_out_t;

  always_ff @(posedge clk) begin
    if (rst)
      cnt_out_t <= 0;
    else begin
      if (operation == cntr_op_state_1)
        cnt_out_t <= 0;
      else if (operation == cntr_op_state_2)
        cnt_out_t <= (1 + cnt_out_t);
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      cnt_out_sig <= 0;
    else begin
      if (operation == cntr_op_state_1)
        cnt_out_sig <= 0;
      else if (operation == cntr_op_state_2)
        cnt_out_sig <= (1 + cnt_out_t);
      else if (operation == cntr_op_state_3)
        cnt_out_sig <= cnt_out_t;
    end
  end

  assign cnt_out_t_out = cnt_out_t;

endmodule
