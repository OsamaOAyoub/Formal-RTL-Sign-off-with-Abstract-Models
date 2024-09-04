// -------------------------------------------------
// Copyright(c) LUBIS EDA GmbH, All rights reserved
// Created on 15.6.2022 at 17:58
// Contact: contact@lubis-eda.com
// Author: Tobias Ludwig, Paulette Iskandar
// -------------------------------------------------

import processor_package::*;

module processor (
    input  logic clk,
    input  logic reset,
    input  TypeInstr instrIn,
    input  TypeDataWord dataIn,
    output TypeDataWord dataOut,
    output TypeInstrAddr instrAddr,
    output TypeDataAddr dataAddr,
    output logic writeEnable
);

    //Registers R0 to R7: each 8 bit wide; R0 is not used
    TypeArrayDataWord REG_FILE;

    ControlStateType CONTROL_STATE;

    TypeInstr IR;
    TypeInstrAddr PC;
    TypeDataAddr DADDR;
    TypeDataWord A, B, DIN, DOUT, TEMP;

    logic DATA_WRITE;

    assign instrAddr = PC;
    assign dataOut = DOUT;
    assign dataAddr = DADDR;
    assign writeEnable = DATA_WRITE;

    always @(posedge clk) begin
        TypeInstrAddr immediate_branch;
        TypeInstrAddr immediate_jump;

        TypeDataWord immediate_alu;
        TypeDataWord operandB;

        DATA_WRITE <= 0;

        if (reset == 1'b1) begin
            CONTROL_STATE <= c_IF;
            PC <= '{default: '0};
            IR <= '{default: '0};
            DOUT <= '0;
            DADDR <= '0;
            REG_FILE <= '0;
            TEMP <= '0;
        end
        else begin
            case(CONTROL_STATE)
                //FETCH
                c_IF: begin
                    PC <= PC + 16'd2;
                    IR <= instrIn;
                    CONTROL_STATE <= c_ID;
                end

                // DECODE
                c_ID: begin
                    if (op1(IR) != c_REG_NULL)
                        A <= REG_FILE[int'(op1(IR))];
                    else
                        A <= c_NULL_WORD;

                    if (op2(IR) != c_REG_NULL)
                        B <= REG_FILE[int'(op2(IR))];
                    else
                        B <= c_NULL_WORD;

                    // Sign extension
                    if (IR[8] == 1'b0)
                        immediate_branch = {c_NULL_BRANCH, IR[8:0]};
                    else
                        immediate_branch = {c_ONE_BRANCH, IR[8:0]};

                    // Sign extension
                    if (IR[11] == 1'b0)
                        immediate_jump = {c_NULL_JUMP, IR[11:0]};
                    else
                        immediate_jump = {c_ONE_JUMP, IR[11:0]};

                    if (opcode(IR) == c_BRANCH) begin
                        if (op1(IR) == c_REG_NULL)
                            PC <= PC + immediate_branch;
                        else if (REG_FILE[int'(op1(IR))] == c_NULL_WORD)
                            PC <= PC + immediate_branch;

                        CONTROL_STATE <= c_IF;
                    end
                    else if (opcode(IR) == c_JUMP) begin
                        PC <= PC + immediate_jump;
                        CONTROL_STATE <= c_IF;
                    end
                    else begin
                        CONTROL_STATE <= c_EX;
                    end
                end

                //EX
                c_EX: begin
                    // Sign extension
                    if (IR[5] == 1'b0)
                        immediate_alu = {c_NULL_ALU, IR[5:0]};
                    else
                        immediate_alu = {c_ONE_ALU, IR[5:0]};

                    if (opcode(IR) == c_STORE) begin
                        DOUT <= B;
                        DATA_WRITE <= 1;
                    end
                    else if (opcode(IR) == c_ALU_REG)
                        operandB = B;
                    else if ((opcode(IR) == c_ADD_IMM) || (opcode(IR) == c_OR_IMM))
                        operandB = immediate_alu;

                    if (((opcode(IR) == c_ALU_REG) && (IR[2:0] == c_ADD)) || (opcode(IR) == c_ADD_IMM))
                        TEMP <= A + operandB;

                    if (((opcode(IR) == c_ALU_REG) && (IR[2:0] == c_OR)) || (opcode(IR) == c_OR_IMM))
                        TEMP <= A | operandB;

                    if ((opcode(IR) == c_LOAD) || (opcode(IR) == c_STORE))
                        DADDR <= A + immediate_alu;

                    CONTROL_STATE <= c_MEM;
                end

                // MEM
                c_MEM: begin
                    if (opcode(IR) == c_LOAD)
                        DIN <= dataIn;
                        CONTROL_STATE <= c_WB;
                    end

                // WB
                c_WB: begin
                    if ((opcode(IR) == c_LOAD) && (op2(IR) != c_REG_NULL))
                        REG_FILE[int'(op2(IR))] <= DIN;
                    else if ((opcode(IR) == c_ALU_REG) && (op3(IR) != c_REG_NULL))
                        REG_FILE[int'(op3(IR))] <= TEMP;
                    else if (((opcode(IR) == c_ADD_IMM) || (opcode(IR) == c_OR_IMM)) && (op2(IR) != c_REG_NULL))
                        REG_FILE[int'(op2(IR))] <= TEMP;

                    CONTROL_STATE <= c_IF;
                end
            endcase
        end
    end

endmodule