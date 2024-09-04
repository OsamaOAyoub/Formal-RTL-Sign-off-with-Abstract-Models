import global_package::*;
import SHA512_operations::*;


module SHA512_control (
  input  bit                 rst,
  input  bit                 clk,
  input  st_SHA_Args         SHA_Input_sig,
  input  bit                 SHA_Input_sync,
  input  bit signed [31:0]   i,
  output SHA512_operations_t operation
);

  typedef enum { SHA512_IDLE, SHA512_SHARounds, SHA512_DONE } SHA512_states_t;

  SHA512_states_t current_state;
  SHA512_states_t next_state;

  always @(current_state, SHA_Input_sig.SHA_Mode, SHA_Input_sig.init, SHA_Input_sync, i)
  begin
    case (current_state)
      SHA512_IDLE:
        begin
          if (SHA_Input_sync && SHA_Input_sig.init && (SHA_Input_sig.SHA_Mode == 224)) begin
            operation <= SHA512_op_IDLE_1;
            next_state <= SHA512_SHARounds;
          end else if (SHA_Input_sync && SHA_Input_sig.init && (SHA_Input_sig.SHA_Mode == 256)) begin
            operation <= SHA512_op_IDLE_2;
            next_state <= SHA512_SHARounds;
          end else if (SHA_Input_sync && SHA_Input_sig.init && (SHA_Input_sig.SHA_Mode == 512)) begin
            operation <= SHA512_op_IDLE_3;
            next_state <= SHA512_SHARounds;
          end else if (SHA_Input_sync && SHA_Input_sig.init && (SHA_Input_sig.SHA_Mode != 224) && (SHA_Input_sig.SHA_Mode != 256) && (SHA_Input_sig.SHA_Mode != 512)) begin
            operation <= SHA512_op_IDLE_4;
            next_state <= SHA512_SHARounds;
          end else if (SHA_Input_sync && !(SHA_Input_sig.init)) begin
            operation <= SHA512_op_IDLE_5;
            next_state <= SHA512_SHARounds;
          end else if (!(SHA_Input_sync)) begin
            operation <= SHA512_op_wait_IDLE;
            next_state <= SHA512_IDLE;
          end
        end
      SHA512_SHARounds:
        begin
          if ((i < 16)) begin
            operation <= SHA512_op_SHARounds_6;
            next_state <= SHA512_SHARounds;
          end else if ((i >= 16) && ((1 + i) < 80)) begin
            operation <= SHA512_op_SHARounds_7;
            next_state <= SHA512_SHARounds;
          end else if ((i >= 16) && ((1 + i) >= 80)) begin
            operation <= SHA512_op_SHARounds_8;
            next_state <= SHA512_DONE;
          end
        end
      SHA512_DONE:
        begin
          if (1) begin
            operation <= SHA512_op_DONE_9;
            next_state <= SHA512_IDLE;
          end
        end
    endcase
  end

  always_ff @(posedge clk)
  begin
    if (rst == 1) begin
      current_state <= SHA512_IDLE;
    end else begin
      current_state <= next_state;
    end
  end

endmodule
