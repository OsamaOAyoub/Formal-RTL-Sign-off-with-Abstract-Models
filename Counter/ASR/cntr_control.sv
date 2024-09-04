import cntr_operations::*;


module cntr_control (
  input  bit                 rst,
  input  bit                 clk,
  input  bit                 en_sig,
  input  bit unsigned [31:0] cnt_out_t,
  output cntr_operations_t   operation
);

  typedef enum { cntr_state } cntr_states_t;

  cntr_states_t current_state;
  cntr_states_t next_state;

  always @(current_state, en_sig, cnt_out_t)
  begin
    case (current_state)
      cntr_state:
        begin
          if (en_sig && (cnt_out_t == 127)) begin
            operation <= cntr_op_state_1;
            next_state <= cntr_state;
          end else if (en_sig && (cnt_out_t != 127)) begin
            operation <= cntr_op_state_2;
            next_state <= cntr_state;
          end else if (!(en_sig)) begin
            operation <= cntr_op_state_3;
            next_state <= cntr_state;
          end
        end
    endcase
  end

  always_ff @(posedge clk)
  begin
    if (rst == 1) begin
      current_state <= cntr_state;
    end else begin
      current_state <= next_state;
    end
  end

endmodule
