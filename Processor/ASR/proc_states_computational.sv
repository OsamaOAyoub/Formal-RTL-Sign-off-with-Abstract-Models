import global_package::*;
import proc_states_package::*;
import proc_states_operations::*;


module proc_states_computational (
  input  bit                      rst,
  input  bit                      clk,
  output bit unsigned [7:0]      dataaddr_sig,
  input  bit unsigned [7:0]      datain_sig,
  output bit unsigned [7:0]      dataout_sig,
  input  bit unsigned [15:0]      instrIn_sig,
  output bit unsigned [15:0]      instraddr_sig,
  output bit                      wen_sig,
  output bit unsigned [15:0]      instr_out,
  output a_sc_unsigned_8_8        reg_file_out,
  input  proc_states_operations_t operation
);

  bit unsigned [7:0] A;
  bit unsigned [7:0] B;
  bit unsigned [15:0] PC;
  bit unsigned [7:0] d_in;
  bit unsigned [15:0] instr;
  bit unsigned [31:0] operandb;
  bit unsigned [31:0] prev_operand;
  a_sc_unsigned_8_8   reg_file;
  bit unsigned [7:0] temp;

  always_ff @(posedge clk) begin
    if (rst)
      A <= 0;
    else begin
      if (operation == proc_states_op_Decode_2 || operation == proc_states_op_Decode_4 || operation == proc_states_op_Decode_5)
        A <= (((instr & 3584) != 0) ? ((((instr >> 9) & 7) == 0) ? reg_file[0] : ((((instr >> 9) & 7) == 1) ? reg_file[1] : ((((instr >> 9) & 7) == 2) ? reg_file[2] : ((((instr >> 9) & 7) == 3) ? reg_file[3] : ((((instr >> 9) & 7) == 4) ? reg_file[4] : ((((instr >> 9) & 7) == 5) ? reg_file[5] : ((((instr >> 9) & 7) == 6) ? reg_file[6] : reg_file[7]))))))) : 0);
      else if (operation == proc_states_op_Decode_3)
        A <= ((((instr >> 9) & 7) == 1) ? reg_file[1] : ((((instr >> 9) & 7) == 2) ? reg_file[2] : ((((instr >> 9) & 7) == 3) ? reg_file[3] : ((((instr >> 9) & 7) == 4) ? reg_file[4] : ((((instr >> 9) & 7) == 5) ? reg_file[5] : ((((instr >> 9) & 7) == 6) ? reg_file[6] : reg_file[7]))))));
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      B <= 0;
    else begin
      if (operation == proc_states_op_Decode_2 || operation == proc_states_op_Decode_3 || operation == proc_states_op_Decode_4 || operation == proc_states_op_Decode_5)
        B <= (((instr & 448) != 0) ? ((((instr >> 6) & 7) == 0) ? reg_file[0] : ((((instr >> 6) & 7) == 1) ? reg_file[1] : ((((instr >> 6) & 7) == 2) ? reg_file[2] : ((((instr >> 6) & 7) == 3) ? reg_file[3] : ((((instr >> 6) & 7) == 4) ? reg_file[4] : ((((instr >> 6) & 7) == 5) ? reg_file[5] : ((((instr >> 6) & 7) == 6) ? reg_file[6] : reg_file[7]))))))) : 0);
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      PC <= 0;
    else begin
      if (operation == proc_states_op_Decode_2)
        PC <= (PC + ((((instr >> 8) & 1) == 1) ? (instr & 511) : (instr | 65024)));
      else if (operation == proc_states_op_Decode_4)
        PC <= (PC + ((((instr >> 11) & 1) == 1) ? (instr & 4095) : (instr | 61440)));
      else if (operation == proc_states_op_Fetch_1)
        PC <= (2 + PC);
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      d_in <= 0;
    else begin
      if (operation == proc_states_op_memory_14)
        d_in <= datain_sig;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      instr <= 0;
    else begin
      if (operation == proc_states_op_Fetch_1)
        instr <= instrIn_sig;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      operandb <= 0;
    else begin
      if (operation == proc_states_op_execute_7 || operation == proc_states_op_execute_8 || operation == proc_states_op_execute_9)
        operandb <= B;
      else if (operation == proc_states_op_execute_10 || operation == proc_states_op_execute_11)
        operandb <= ((((instr >> 5) & 1) == 0) ? (instr & 63) : (192 | (instr & 63)));
      else if (operation == proc_states_op_writeback_16 || operation == proc_states_op_writeback_17 || operation == proc_states_op_writeback_18 || operation == proc_states_op_writeback_19)
        operandb <= prev_operand;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      prev_operand <= 0;
    else begin
      if (operation == proc_states_op_memory_14 || operation == proc_states_op_memory_15)
        prev_operand <= operandb;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      reg_file[0] <= 0;
  end

  always_ff @(posedge clk) begin
    if (rst)
      reg_file[1] <= 0;
    else begin
      if (operation == proc_states_op_writeback_16)
        reg_file[1] <= ((((instr >> 6) & 7) == 1) ? d_in : reg_file[1]);
      else if (operation == proc_states_op_writeback_17)
        reg_file[1] <= ((((instr >> 3) & 7) == 1) ? temp : reg_file[1]);
      else if (operation == proc_states_op_writeback_18)
        reg_file[1] <= ((((instr >> 6) & 7) == 1) ? temp : reg_file[1]);
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      reg_file[2] <= 0;
    else begin
      if (operation == proc_states_op_writeback_16)
        reg_file[2] <= ((((instr >> 6) & 7) == 2) ? d_in : reg_file[2]);
      else if (operation == proc_states_op_writeback_17)
        reg_file[2] <= ((((instr >> 3) & 7) == 2) ? temp : reg_file[2]);
      else if (operation == proc_states_op_writeback_18)
        reg_file[2] <= ((((instr >> 6) & 7) == 2) ? temp : reg_file[2]);
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      reg_file[3] <= 0;
    else begin
      if (operation == proc_states_op_writeback_16)
        reg_file[3] <= ((((instr >> 6) & 7) == 3) ? d_in : reg_file[3]);
      else if (operation == proc_states_op_writeback_17)
        reg_file[3] <= ((((instr >> 3) & 7) == 3) ? temp : reg_file[3]);
      else if (operation == proc_states_op_writeback_18)
        reg_file[3] <= ((((instr >> 6) & 7) == 3) ? temp : reg_file[3]);
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      reg_file[4] <= 0;
    else begin
      if (operation == proc_states_op_writeback_16)
        reg_file[4] <= ((((instr >> 6) & 7) == 4) ? d_in : reg_file[4]);
      else if (operation == proc_states_op_writeback_17)
        reg_file[4] <= ((((instr >> 3) & 7) == 4) ? temp : reg_file[4]);
      else if (operation == proc_states_op_writeback_18)
        reg_file[4] <= ((((instr >> 6) & 7) == 4) ? temp : reg_file[4]);
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      reg_file[5] <= 0;
    else begin
      if (operation == proc_states_op_writeback_16)
        reg_file[5] <= ((((instr >> 6) & 7) == 5) ? d_in : reg_file[5]);
      else if (operation == proc_states_op_writeback_17)
        reg_file[5] <= ((((instr >> 3) & 7) == 5) ? temp : reg_file[5]);
      else if (operation == proc_states_op_writeback_18)
        reg_file[5] <= ((((instr >> 6) & 7) == 5) ? temp : reg_file[5]);
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      reg_file[6] <= 0;
    else begin
      if (operation == proc_states_op_writeback_16)
        reg_file[6] <= ((((instr >> 6) & 7) == 6) ? d_in : reg_file[6]);
      else if (operation == proc_states_op_writeback_17)
        reg_file[6] <= ((((instr >> 3) & 7) == 6) ? temp : reg_file[6]);
      else if (operation == proc_states_op_writeback_18)
        reg_file[6] <= ((((instr >> 6) & 7) == 6) ? temp : reg_file[6]);
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      reg_file[7] <= 0;
    else begin
      if (operation == proc_states_op_writeback_16)
        reg_file[7] <= ((((instr >> 6) & 7) == 7) ? d_in : reg_file[7]);
      else if (operation == proc_states_op_writeback_17)
        reg_file[7] <= ((((instr >> 3) & 7) == 7) ? temp : reg_file[7]);
      else if (operation == proc_states_op_writeback_18)
        reg_file[7] <= ((((instr >> 6) & 7) == 7) ? temp : reg_file[7]);
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      temp <= 0;
    else begin
      if (operation == proc_states_op_execute_7)
        temp <= (A + B);
      else if (operation == proc_states_op_execute_8)
        temp <= (A | B);
      else if (operation == proc_states_op_execute_10)
        temp <= (A + ((((instr >> 5) & 1) == 0) ? (instr & 63) : (192 | (instr & 63))));
      else if (operation == proc_states_op_execute_11)
        temp <= (A | ((((instr >> 5) & 1) == 0) ? (instr & 63) : (192 | (instr & 63))));
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      dataaddr_sig <= 0;
    else begin
      if (operation == proc_states_op_execute_6 || operation == proc_states_op_execute_12)
        dataaddr_sig <= (A + ((((instr >> 5) & 1) == 0) ? (instr & 63) : (192 | (instr & 63))));
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      dataout_sig <= 0;
    else begin
      if (operation == proc_states_op_execute_6)
        dataout_sig <= B;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      instraddr_sig <= 0;
    else begin
      if (operation == proc_states_op_Decode_2)
        instraddr_sig <= (PC + ((((instr >> 8) & 1) == 1) ? (instr & 511) : (instr | 65024)));
      else if (operation == proc_states_op_Decode_4)
        instraddr_sig <= (PC + ((((instr >> 11) & 1) == 1) ? (instr & 4095) : (instr | 61440)));
      else if (operation == proc_states_op_Fetch_1)
        instraddr_sig <= (2 + PC);
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      wen_sig <= 0;
    else begin
      if (operation == proc_states_op_execute_6)
        wen_sig <= 1;
      else if (operation == proc_states_op_memory_14 || operation == proc_states_op_memory_15)
        wen_sig <= 0;
    end
  end

  assign instr_out    = instr;
  assign reg_file_out = reg_file;

endmodule
