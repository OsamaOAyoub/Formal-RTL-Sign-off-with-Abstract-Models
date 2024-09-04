import global_package::*;
import proc_states_package::*;
import proc_states_operations::*;


module proc_states_control (
  input  bit                      rst,
  input  bit                      clk,
  input  bit unsigned [15:0]      instr,
  input  a_sc_unsigned_8_8        reg_file,
  output proc_states_operations_t operation
);

  typedef enum { proc_states_Fetch, proc_states_Decode, proc_states_execute, proc_states_memory, proc_states_writeback } proc_states_states_t;

  proc_states_states_t current_state;
  proc_states_states_t next_state;

  always @(current_state, instr, reg_file[0], reg_file[7])
  begin
    case (current_state)
      proc_states_Fetch:
        begin
          if (1) begin
            operation <= proc_states_op_Fetch_1;
            next_state <= proc_states_Decode;
          end
        end
      proc_states_Decode:
        begin
          if (((instr >> 12) == 7) && (((instr & 3584) == 0) || ((((instr & 3584) == 0) ? reg_file[0] : reg_file[7]) == 0))) begin
            operation <= proc_states_op_Decode_2;
            next_state <= proc_states_Fetch;
          end else if (((instr >> 12) == 7) && !((((instr & 3584) == 0) || (reg_file[7] == 0)))) begin
            operation <= proc_states_op_Decode_3;
            next_state <= proc_states_Fetch;
          end else if (((instr >> 12) == 6)) begin
            operation <= proc_states_op_Decode_4;
            next_state <= proc_states_Fetch;
          end else if (((instr >> 12) != 7) && ((instr >> 12) != 6)) begin
            operation <= proc_states_op_Decode_5;
            next_state <= proc_states_execute;
          end
        end
      proc_states_execute:
        begin
          if (((instr >> 12) == 5) && !(((((instr >> 12) == 1) && ((instr & 7) == 1)) || ((instr >> 12) == 2))) && !(((((instr >> 12) == 1) && ((instr & 7) == 2)) || ((instr >> 12) == 3))) && (((instr >> 12) == 4) || ((instr >> 12) == 5))) begin
            operation <= proc_states_op_execute_6;
            next_state <= proc_states_memory;
          end else if (((instr >> 12) == 1) && ((((instr >> 12) == 1) && ((instr & 7) == 1)) || ((instr >> 12) == 2)) && !(((((instr >> 12) == 1) && ((instr & 7) == 2)) || ((instr >> 12) == 3))) && !((((instr >> 12) == 4) || ((instr >> 12) == 5)))) begin
            operation <= proc_states_op_execute_7;
            next_state <= proc_states_memory;
          end else if (((instr >> 12) == 1) && !(((((instr >> 12) == 1) && ((instr & 7) == 1)) || ((instr >> 12) == 2))) && ((((instr >> 12) == 1) && ((instr & 7) == 2)) || ((instr >> 12) == 3)) && !((((instr >> 12) == 4) || ((instr >> 12) == 5)))) begin
            operation <= proc_states_op_execute_8;
            next_state <= proc_states_memory;
          end else if (((instr >> 12) == 1) && !(((((instr >> 12) == 1) && ((instr & 7) == 1)) || ((instr >> 12) == 2))) && !(((((instr >> 12) == 1) && ((instr & 7) == 2)) || ((instr >> 12) == 3))) && !((((instr >> 12) == 4) || ((instr >> 12) == 5)))) begin
            operation <= proc_states_op_execute_9;
            next_state <= proc_states_memory;
          end else if (((instr >> 12) != 5) && ((instr >> 12) != 1) && (((instr >> 12) == 2) || ((instr >> 12) == 3)) && ((((instr >> 12) == 1) && ((instr & 7) == 1)) || ((instr >> 12) == 2)) && !(((((instr >> 12) == 1) && ((instr & 7) == 2)) || ((instr >> 12) == 3))) && !((((instr >> 12) == 4) || ((instr >> 12) == 5)))) begin
            operation <= proc_states_op_execute_10;
            next_state <= proc_states_memory;
          end else if (((instr >> 12) != 5) && ((instr >> 12) != 1) && (((instr >> 12) == 2) || ((instr >> 12) == 3)) && !(((((instr >> 12) == 1) && ((instr & 7) == 1)) || ((instr >> 12) == 2))) && ((((instr >> 12) == 1) && ((instr & 7) == 2)) || ((instr >> 12) == 3)) && !((((instr >> 12) == 4) || ((instr >> 12) == 5)))) begin
            operation <= proc_states_op_execute_11;
            next_state <= proc_states_memory;
          end else if (((instr >> 12) != 5) && ((instr >> 12) != 1) && !((((instr >> 12) == 2) || ((instr >> 12) == 3))) && !(((((instr >> 12) == 1) && ((instr & 7) == 1)) || ((instr >> 12) == 2))) && !(((((instr >> 12) == 1) && ((instr & 7) == 2)) || ((instr >> 12) == 3))) && (((instr >> 12) == 4) || ((instr >> 12) == 5))) begin
            operation <= proc_states_op_execute_12;
            next_state <= proc_states_memory;
          end else if (((instr >> 12) != 5) && ((instr >> 12) != 1) && !((((instr >> 12) == 2) || ((instr >> 12) == 3))) && !(((((instr >> 12) == 1) && ((instr & 7) == 1)) || ((instr >> 12) == 2))) && !(((((instr >> 12) == 1) && ((instr & 7) == 2)) || ((instr >> 12) == 3))) && !((((instr >> 12) == 4) || ((instr >> 12) == 5)))) begin
            operation <= proc_states_op_execute_13;
            next_state <= proc_states_memory;
          end
        end
      proc_states_memory:
        begin
          if (((instr >> 12) == 4)) begin
            operation <= proc_states_op_memory_14;
            next_state <= proc_states_writeback;
          end else if (((instr >> 12) != 4)) begin
            operation <= proc_states_op_memory_15;
            next_state <= proc_states_writeback;
          end
        end
      proc_states_writeback:
        begin
          if ((((instr >> 12) == 4) && ((instr & 448) != 0)) && !((((instr >> 12) == 1) && (((instr >> 3) & 7) != 0))) && !(((((instr >> 12) == 2) || ((instr >> 12) == 3)) && ((instr & 448) != 0)))) begin
            operation <= proc_states_op_writeback_16;
            next_state <= proc_states_Fetch;
          end else if (!((((instr >> 12) == 4) && ((instr & 448) != 0))) && (((instr >> 12) == 1) && (((instr >> 3) & 7) != 0))) begin
            operation <= proc_states_op_writeback_17;
            next_state <= proc_states_Fetch;
          end else if (!((((instr >> 12) == 4) && ((instr & 448) != 0))) && !((((instr >> 12) == 1) && (((instr >> 3) & 7) != 0))) && ((((instr >> 12) == 2) || ((instr >> 12) == 3)) && ((instr & 448) != 0))) begin
            operation <= proc_states_op_writeback_18;
            next_state <= proc_states_Fetch;
          end else if (!((((instr >> 12) == 4) && ((instr & 448) != 0))) && !((((instr >> 12) == 1) && (((instr >> 3) & 7) != 0))) && !(((((instr >> 12) == 2) || ((instr >> 12) == 3)) && ((instr & 448) != 0)))) begin
            operation <= proc_states_op_writeback_19;
            next_state <= proc_states_Fetch;
          end
        end
    endcase
  end

  always_ff @(posedge clk)
  begin
    if (rst == 1) begin
      current_state <= proc_states_Fetch;
    end else begin
      current_state <= next_state;
    end
  end

endmodule

