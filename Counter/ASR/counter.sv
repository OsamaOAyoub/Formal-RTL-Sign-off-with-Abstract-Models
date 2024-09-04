module counter #(
    parameter N = 7
)(
    input logic clk,
    input logic rst,
    input logic en,
    output logic [N-1:0] cnt
);

logic en_1,en_2;

always_ff @(posedge clk, posedge rst) begin

    if(rst) begin
        
        cnt <= '0;
        en_1 <= '0;
        en_2 <= '0;

    end
    else begin

        en_1 <= en;
        en_2 <= en_1;

        if(en_2) begin
            cnt <= cnt+1;
        end

    end

end

endmodule
