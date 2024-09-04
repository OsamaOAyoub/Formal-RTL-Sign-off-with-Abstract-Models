//`define N 15
//`define M 5
//Convert to package
/*verilator --cc +1800-2012ext+sv OptionsParser.sv */

package optionsPackage;
typedef enum {START,ENDOPTION,INFO,INFOCONTENTS,DATA,DATALEN,DATACONTENTS} options; 

const bit unsigned [31:0] M = 5;
const bit unsigned [31:0] N = 15;
typedef struct packed{
    options OptionType;
    bit unsigned [3:0] position;
    bit unsigned [7:0] contents;
} Field;

typedef struct packed{
    Field startOption;
    Field endOption;
    Field infoOption;
    Field infoOptionContents;
    Field dataOption;
    Field dataOptionLen;
    Field  [4:0] dataOptionContents;
    logic hasStart;
    logic hasInfo;
    logic hasData;
    logic hasEnd;
    logic isEmpty;
    logic hasError;
} ParsedOptions;

endpackage

import optionsPackage::*;

module OptionsParserRTL(
    input logic clk,
    input logic rst,
    input bit unsigned [7:0] fieldIn[14:0], 
    input logic startParsing,
    output ParsedOptions parsed,
    output logic busy,
    output logic done,
    output logic ready,
    input logic read
);

bit unsigned [3:0] counter; //Change width if N is greater than 15
byte unsigned DataCounter;
logic dataFlag;
logic dataLenFlag;
logic InfoFlag;
logic dataDone;
bit unsigned [7:0] field[14:0];

//bugs
logic EasyBug;
logic MediumBug;
logic MediumBugCtrl;
logic hardBug;
logic hardBugCtrl;
bit unsigned [31:0] hardBugCounter;
//enum {IDLE, PARSING,DONEPARSING} state_s;
enum {READY, STARTPARSING,DATAPARSING, INFOPARSING, ENDPARSING, DONEPARSING} state_s;

always @(posedge clk or posedge rst)
begin
    if(rst) begin
        parsed.hasStart <= 1'b0;
        parsed.hasInfo <= 1'b0;
        parsed.hasData <= 1'b0;
        parsed.hasEnd <= 1'b0;
        parsed.isEmpty <= 1'b1;
        parsed.hasError <= 1'b0;
        counter <= 8'h0;
        DataCounter <= 8'h0;
        busy <= 1'b0;
        done <= 1'b0;
        ready <= 1'b1;
        dataFlag <= 1'b0;
        dataLenFlag <= 1'b0;
        InfoFlag <= 1'b0;
        dataDone <= 1'b0;
        //state_s <= INITSTATEREAD;
        state_s <= READY;


        parsed.dataOption.contents <= 0;
        parsed.dataOption.position <= 0;
        parsed.dataOption.OptionType <= options'(START);
        parsed.dataOptionContents[0].contents <= 0;
        parsed.dataOptionContents[0].position <= 0;
        parsed.dataOptionContents[0].OptionType <= options'(START);
        parsed.dataOptionContents[1].contents <= 0;
        parsed.dataOptionContents[1].position <= 0;
        parsed.dataOptionContents[1].OptionType <= options'(START);
        parsed.dataOptionContents[2].contents <= 0;
        parsed.dataOptionContents[2].position <= 0;
        parsed.dataOptionContents[2].OptionType <= options'(START);
        parsed.dataOptionContents[3].contents <= 0;
        parsed.dataOptionContents[3].position <= 0;
        parsed.dataOptionContents[3].OptionType <= options'(START);
        parsed.dataOptionContents[4].contents <= 0;
        parsed.dataOptionContents[4].position <= 0;
        parsed.dataOptionContents[4].OptionType <= options'(START);
        parsed.dataOptionLen.contents <= 0;
        parsed.dataOptionLen.position <= 0;
        parsed.dataOptionLen.OptionType <= options'(START);
        parsed.endOption.contents <= 0;
        parsed.endOption.position <= 0;
        parsed.endOption.OptionType <= options'(START);
        parsed.infoOption.contents <= 0;
        parsed.infoOption.position <= 0;
        parsed.infoOption.OptionType <= options'(START);
        parsed.infoOptionContents.contents <= 0;
        parsed.infoOptionContents.position <= 0;
        parsed.infoOptionContents.OptionType <= options'(START);
        parsed.startOption.contents <= 0;
        parsed.startOption.position <= 0;
        parsed.startOption.OptionType <= options'(START);
        parsed.hasData <= 0;
        parsed.hasInfo <= 0;
        parsed.hasStart <= 0;
        parsed.hasEnd <= 0;
        parsed.hasError <= 0;
        parsed.isEmpty <= 0;
    end
    else begin
            case (state_s)
                //INITSTATEREAD: begin
                //    state_s <= READY;
                //end
                READY: begin
                    if(startParsing) begin
                        EasyBug <= 1'b0;
                        MediumBugCtrl <= 1'b0;
                        hardBugCtrl <= 1'b0;
                        hardBugCounter <= 0;
                        state_s <= STARTPARSING;
                        busy <= 1'b1;
                        ready <= 1'b0;
                        parsed.dataOption.contents <= 0;
        parsed.dataOption.position <= 0;
        parsed.dataOption.OptionType <= options'(START);
        parsed.dataOptionContents[0].contents <= 0;
        parsed.dataOptionContents[0].position <= 0;
        parsed.dataOptionContents[0].OptionType <= options'(START);
        parsed.dataOptionContents[1].contents <= 0;
        parsed.dataOptionContents[1].position <= 0;
        parsed.dataOptionContents[1].OptionType <= options'(START);
        parsed.dataOptionContents[2].contents <= 0;
        parsed.dataOptionContents[2].position <= 0;
        parsed.dataOptionContents[2].OptionType <= options'(START);
        parsed.dataOptionContents[3].contents <= 0;
        parsed.dataOptionContents[3].position <= 0;
        parsed.dataOptionContents[3].OptionType <= options'(START);
        parsed.dataOptionContents[4].contents <= 0;
        parsed.dataOptionContents[4].position <= 0;
        parsed.dataOptionContents[4].OptionType <= options'(START);
        parsed.dataOptionLen.contents <= 0;
        parsed.dataOptionLen.position <= 0;
        parsed.dataOptionLen.OptionType <= options'(START);
        parsed.endOption.contents <= 0;
        parsed.endOption.position <= 0;
        parsed.endOption.OptionType <= options'(START);
        parsed.infoOption.contents <= 0;
        parsed.infoOption.position <= 0;
        parsed.infoOption.OptionType <= options'(START);
        parsed.infoOptionContents.contents <= 0;
        parsed.infoOptionContents.position <= 0;
        parsed.infoOptionContents.OptionType <= options'(START);
        parsed.startOption.contents <= 0;
        parsed.startOption.position <= 0;
        parsed.startOption.OptionType <= options'(START);
        parsed.hasData <= 0;
        parsed.hasInfo <= 0;
        parsed.hasStart <= 0;
        parsed.hasEnd <= 0;
        parsed.hasError <= 0;
        parsed.isEmpty <= 0;
        counter <= 8'h0;

                        field <= fieldIn; 
                    end
                    else begin
                        busy <= 1'b0;
                        ready <= 1'b1; 
                    end
                    done <= 1'b0;
                    
                    DataCounter <= 8'h0;
                    dataFlag <= 1'b0;
                    dataLenFlag <= 1'b0;
                    InfoFlag <= 1'b0;
                    dataDone <= 1'b0;
                            
                end
                STARTPARSING: begin
                    if(counter < N) begin
                        if(field[counter] == 1 ) begin
                            parsed.startOption.position <= counter;
                            parsed.startOption.contents <= 1;
                            parsed.startOption.OptionType <= options'(START);
                            parsed.hasStart <= 1'b1;
                            counter <= counter + 1;
                            if(hardBugCtrl) begin
                                hardBugCounter <= hardBugCounter + 1;
                            end
                            if(hardBugCtrl && hardBugCounter == 3) begin
                                hardBug <= 1'b1;
                            end
                            else begin
                                hardBug <= 1'b0;
                            end
                        end
                        else if(field[counter] == 2 && parsed.hasStart) begin
                            state_s <= ENDPARSING;
                        end
                        else if(field[counter] == 3 && parsed.hasStart) begin
                            state_s <= INFOPARSING;
                            //counter <= counter + 1;
                        end
                        else if(field[counter] == 4 && parsed.hasStart && counter < N-3) begin //12
                            state_s <= DATAPARSING;
                            if(field[counter + 1] > M || field[counter + 1] + counter + 1 > N-2) begin //13
                                parsed.hasError <= 1'b1;
                            end
                            //Med bug
                            if(field[counter + 1] == 8'h43 && MediumBugCtrl) begin
                                MediumBug <= 1'b1;
                            end
                            else begin
                                MediumBug <= 1'b0;
                            end
                            counter <= counter + 1;
                        end
                        else begin
                            counter <= counter + 1;
                        end
                    end
                    else begin
                        if(parsed.hasStart) begin
                            parsed.hasError <= 1'b1;
                        end
                        else begin
                            parsed.isEmpty <= 1'b1;
                        end
                        state_s <= DONEPARSING;
                        done <= 1'b1;
                    end


                end
                INFOPARSING: begin
                    if(counter < N) begin
                        if(parsed.hasInfo != 1'b1 && counter < N-2) begin //13
                            parsed.infoOption.position <= counter;
                            parsed.infoOption.contents <= 3;
                            parsed.infoOption.OptionType <= options'(INFO);
                            parsed.hasInfo <= 1'b1;
                            parsed.infoOptionContents.position <= counter + 1;
                            parsed.infoOptionContents.contents <= field[counter + 1];
                            parsed.infoOptionContents.OptionType <= options'(INFOCONTENTS);
                            //if(counter > 12 || parsed.hasStart == 1'b0) begin // > 15 - 3 = 12 , 15 here is the max length of the sequence
                            //    parsed.hasError <= 1'b1;
                            //    state_s <= DONEPARSING;
                            //end
                            parsed.isEmpty <= 1'b0;
                            //InfoFlag <=  1'b1;
                            counter <= counter + 2;
                        end
                        else begin
                            if(field[counter] == 2) begin
                                state_s <= ENDPARSING;
                            end
                            else if(field[counter] == 4 && !parsed.hasData && counter < N-3) begin //12
                                state_s <= DATAPARSING;
                                if(field[counter + 1] > M || field[counter + 1] + counter + 1 > N-2) begin //13
                                    parsed.hasError <= 1'b1;
                                end
                                //Med bug
                                if(field[counter + 1] == 8'h43 && MediumBugCtrl) begin
                                    MediumBug <= 1'b1;
                                end
                                else begin
                                    MediumBug <= 1'b0;
                                end
                                counter <= counter + 1;
                            end
                            else begin
                                counter <= counter + 1;
                            end
                        end
                    end
                    else begin
                        parsed.hasError <= 1'b1;
                        state_s <= DONEPARSING;
                        done <= 1'b1;      
                    end
                end
                DATAPARSING: begin
                    if(counter < N && !parsed.hasError || MediumBug) begin
                        if(parsed.hasData != 1'b1 && (counter < N-2 || field[counter] == 0)) begin  //13
                            parsed.dataOption.position <= counter - 1;
                            parsed.dataOption.contents <= 4; 
                            parsed.dataOption.OptionType <= options'(DATA);
                            parsed.hasData <= 1'b1;
                            //dataFlag <= 1'b1;
                            parsed.isEmpty <= 1'b0;
                        end
                        if(dataLenFlag != 1'b1 && (counter < N-2 || field[counter] == 0)) begin //13
                            parsed.dataOptionLen.position <= counter;  
                            if(!EasyBug) begin       
                                parsed.dataOptionLen.contents <= field[counter];

                            end
                            else begin
                                parsed.dataOptionLen.contents <= field[counter] + 1;
                            end
                            if(field[counter] == 0) begin
                                dataDone <= 1'b1;
                            end
                            parsed.dataOptionLen.OptionType <= options'(DATALEN);
                            if(field[counter] > M || field[counter] + counter > N-2 || parsed.hasStart == 1'b0 || parsed.hasError && !MediumBug) begin //5 is max data length, 13 is N-2
                                parsed.hasError <= 1'b1;
                                state_s <= DONEPARSING;
                                done <= 1'b1;
                            end
                            else begin
                                
                                dataLenFlag <= 1'b1;
                                counter <= counter + 1;
                            end
                        end
                        if(parsed.hasData == 1'b1 && dataLenFlag == 1'b1 && !dataDone && parsed.dataOptionLen.contents  != 0) begin
                            parsed.dataOptionContents[DataCounter].position <= counter;
                            parsed.dataOptionContents[DataCounter].contents <= field[counter]; 
                            parsed.dataOptionContents[DataCounter].OptionType <= options'(DATACONTENTS);
                            DataCounter <= DataCounter + 1;                  
                            counter <= counter + 1;
                            if(DataCounter == parsed.dataOptionLen.contents - 1) begin
                                dataDone <= 1'b1;
                            end
                        end
                        //else if(parsed.dataOptionLen.contents  == 0 && !dataDone) begin
                        //    dataDone <= 1'b1;
                        //end

                        else if(field[counter] == 2 && dataDone) begin
                            state_s <= ENDPARSING;
                        end
                        else if(field[counter] == 3 && dataDone && !parsed.hasInfo) begin
                            state_s <= INFOPARSING;
                        end
                        else  begin
                            counter <= counter + 1;
                        end
                    end
                    else begin
                        parsed.hasError <= 1'b1;
                        state_s <= DONEPARSING;
                        done <= 1'b1;
                    end
                end
                ENDPARSING: begin
                    parsed.endOption.position <= counter;
                    parsed.endOption.contents <= 2;
                    parsed.endOption.OptionType <= options'(ENDOPTION);
                    parsed.hasEnd <= 1'b1;

                    if((!parsed.hasData && !parsed.hasInfo && parsed.hasStart)) begin
                        parsed.isEmpty <= 1'b1;
                    end
                    
                    if(parsed.hasStart == 1'b0) begin
                        parsed.hasError <= 1'b1;
                    end
                    state_s <= DONEPARSING;

                    if(hardBug && parsed.hasData && parsed.hasInfo) begin
                        parsed.hasData <= 1'b0;
                        parsed.dataOption.position <= 16'h1234;
                        parsed.isEmpty <= 1'b1;
                    end
                    done <= 1'b1;
                end
               // PARSING: begin
               //     if(counter < 15) begin
               //         if(field[counter] == 1 && dataLenFlag != 1'b1 && dataFlag != 1'b1 && InfoFlag != 1'b1) begin
               //             parsed.startOption.position <= counter;
               //             parsed.startOption.contents <= 1;
               //             parsed.startOption.OptionType <= options'(START);
               //             parsed.hasStart <= 1'b1;
               //             counter <= counter + 1;
               //         end
               //         else if(field[counter] == 2 && dataLenFlag != 1'b1 && dataFlag != 1'b1 && InfoFlag != 1'b1) begin
               //             parsed.endOption.position <= counter;
               //             parsed.endOption.contents = 2;
               //             parsed.endOption.OptionType = ENDOPTION;
               //             parsed.hasEnd <= 1'b1;
               //             if(parsed.hasStart == 1'b0) begin
               //                 parsed.hasError <= 1'b1;
               //             end
               //             state_s <= DONEPARSING;
               //         end
               //         else if(field[counter] == 3 && dataLenFlag != 1'b1 && dataFlag != 1'b1 && InfoFlag != 1'b1) begin
               //             parsed.infoOption.position <= counter;
               //             parsed.infoOption.contents <= 3;
               //             parsed.infoOption.OptionType <= INFO;
               //             parsed.hasInfo <= 1'b1;
               //             if(counter > 12 || parsed.hasStart == 1'b0) begin // > 15 - 3 = 12 , 15 here is the max length of the sequence
               //                 parsed.hasError <= 1'b1;
               //                 state_s <= DONEPARSING;
               //             end
               //             counter <= counter + 1;
               //             parsed.isEmpty <= 1'b0;
               //             InfoFlag <=  1'b1;
               //         end
               //         else if(dataLenFlag != 1'b1 && dataFlag != 1'b1 && InfoFlag == 1'b1) begin
               //             parsed.infoOptionContents.position <= counter;
               //             parsed.infoOptionContents.contents <= field[counter];
               //             parsed.infoOptionContents.OptionType <= INFOCONTENTS;
               //             counter <= counter + 1;
               //             InfoFlag <=  1'b0;
               //         end
               //         else if(field[counter] == 4 && dataLenFlag != 1'b1 && dataFlag != 1'b1) begin
               //             parsed.dataOption.position <= counter;
               //             parsed.dataOption.contents <= 4; 
               //             parsed.dataOption.OptionType = DATA;
               //             parsed.hasData <= 1'b1;
               //             dataLenFlag <= 1'b1;
               //             counter <= counter + 1;
               //             parsed.isEmpty <= 1'b0;
               //         end
               //         else if(dataLenFlag == 1'b1 && dataFlag != 1'b1) begin
               //             parsed.dataOptionLen.position <= counter;         
               //             parsed.dataOptionLen.contents <= field[counter];
               //             if(field[counter] > 5 || field[counter] + counter > 13 || parsed.hasStart == 1'b0) begin //5 is max data length, 13 is N-2
               //                 parsed.hasError <= 1'b1;
               //                 state_s <= DONEPARSING;
               //             end
               //             parsed.dataOptionLen.OptionType <= DATALEN;
               //             dataFlag <= 1'b1;
               //             counter <= counter + 1;
               //         end
               //         else if(dataFlag == 1'b1) begin
               //             parsed.dataOptionContents[counter].position <= counter;
               //             parsed.dataOptionContents[counter].contents <= field[counter]; 
               //             parsed.dataOptionContents[counter].OptionType <= DATACONTENTS;
               //             DataCounter <= DataCounter + 1;                  
               //             counter <= counter + 1;
               //             if(DataCounter == parsed.dataOptionLen.contents - 1) begin
               //                 dataFlag <= 1'b0;
               //                 dataLenFlag <= 1'b0;
               //             end
               //         end
               //         else begin
               //             counter <= counter + 1;
               //         end
               //     end
               //     else begin
               //         if(parsed.hasEnd == 1'b0 && parsed.hasStart == 1'b1) begin
               //             parsed.hasError <= 1'b1;
               //         end
               //         state_s <= DONEPARSING;
               //     end  
               // end    
                DONEPARSING: begin
                        busy <= 1'b0;
                        done <= 1'b1;
                        if(read && done) begin
                            state_s <= READY;
                            done <= 1'b0;
                            ready <= 1'b1;
                        end

                end
                //LASTSTATE: begin
                //    state_s <= INITSTATEREAD;
                //end 
            endcase

            
                    
    end

end
endmodule