package processor_package;

    typedef enum reg [2:0] {c_IF = 1, c_ID, c_EX, c_MEM, c_WB} ControlStateType;

    typedef logic [15:0] TypeInstr;
    typedef logic [15:0] TypeInstrAddr;

    typedef logic [7:0] TypeDataAddr;
    typedef logic [7:0] TypeDataWord;

    typedef logic [2:0] TypeRegAddr;
    typedef logic [8:0] TypeExInstr;

    typedef logic [3:0] TypeOpcode;
    typedef logic [2:0] TypeAluOp;

    // 8 registers -- 1byte each
    typedef TypeDataWord [7:0] TypeArrayDataWord;

    parameter TypeOpcode c_ALU_REG = 4'b0001;

    parameter TypeOpcode c_ADD_IMM = 4'b0010;
    parameter TypeOpcode c_OR_IMM  = 4'b0011;

    parameter TypeOpcode c_LOAD    = 4'b0100;
    parameter TypeOpcode c_STORE   = 4'b0101;

    parameter TypeOpcode c_JUMP    = 4'b0110;
    parameter TypeOpcode c_BRANCH  = 4'b0111;

    parameter TypeAluOp c_ADD = 3'b001;
    parameter TypeAluOp c_OR  = 3'b010;

    parameter logic [2:0] c_REG_NULL  = '{default: '0};
    parameter logic [7:0] c_NULL_WORD = '{default: '0};

    parameter logic [1:0] c_NULL_ALU  = '{default: '0};
    parameter logic [1:0] c_ONE_ALU   = '{default: '1};

    parameter logic [6:0] c_NULL_BRANCH = '{default: '0};
    parameter logic [6:0] c_ONE_BRANCH  = '{default: '1};

    parameter logic [3:0] c_NULL_JUMP = '{default: '0};
    parameter logic [3:0] c_ONE_JUMP  = '{default: '1};

    function TypeOpcode opcode(TypeInstr ir);
        return ir[15:12];
    endfunction

    function TypeAluOp op1(TypeInstr ir);
        return ir[11:9];
    endfunction

    function TypeAluOp op2(TypeInstr ir);
        return ir[8:6];
    endfunction

    function TypeAluOp op3(TypeInstr ir);
        return ir[5:3];
    endfunction

endpackage