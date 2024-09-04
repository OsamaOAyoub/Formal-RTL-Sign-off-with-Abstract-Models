import global_package::*;
import SHA512_operations::*;


module SHA512_computational (
  input  bit                  rst,
  input  bit                  clk,
  input  st_SHA_Args          SHA_Input_sig,
  output bit                  SHA_Input_notify,
  output bit unsigned [511:0] out_sig,
  output bit                  out_notify,
  output bit signed [31:0]    i_out,
  input  SHA512_operations_t  operation
);

  a_sc_big_unsigned_64_8  H;
  a_sc_big_unsigned_64_16 W;
  bit unsigned [63:0]     a;
  bit unsigned [63:0]     b;
  bit unsigned [63:0]     c;
  bit unsigned [63:0]     d;
  bit unsigned [63:0]     e;
  bit unsigned [63:0]     f;
  bit unsigned [63:0]     g;
  bit unsigned [63:0]     h;
  bit signed [31:0]       i;

  always_ff @(posedge clk) begin
    if (rst)
      H[0] <= 64'd0;
    else begin
      if (operation == SHA512_op_DONE_9)
        H[0] <= 64'((H[0] + a));
      else if (operation == SHA512_op_IDLE_1)
        H[0] <= 64'd10105294471447203234;
      else if (operation == SHA512_op_IDLE_2)
        H[0] <= 64'd2463787394917988140;
      else if (operation == SHA512_op_IDLE_3)
        H[0] <= 64'd7640891576956012808;
      else if (operation == SHA512_op_IDLE_4)
        H[0] <= 64'd14680500436340154072;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      H[1] <= 64'd0;
    else begin
      if (operation == SHA512_op_DONE_9)
        H[1] <= 64'((H[1] + b));
      else if (operation == SHA512_op_IDLE_1)
        H[1] <= 64'd8350123849800275158;
      else if (operation == SHA512_op_IDLE_2)
        H[1] <= 64'd11481187982095705282;
      else if (operation == SHA512_op_IDLE_3)
        H[1] <= 64'd13503953896175478587;
      else if (operation == SHA512_op_IDLE_4)
        H[1] <= 64'd7105036623409894663;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      H[2] <= 64'd0;
    else begin
      if (operation == SHA512_op_DONE_9)
        H[2] <= 64'((H[2] + c));
      else if (operation == SHA512_op_IDLE_1)
        H[2] <= 64'd2160240930085379202;
      else if (operation == SHA512_op_IDLE_2)
        H[2] <= 64'd2563595384472711505;
      else if (operation == SHA512_op_IDLE_3)
        H[2] <= 64'd4354685564936845355;
      else if (operation == SHA512_op_IDLE_4)
        H[2] <= 64'd10473403895298186519;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      H[3] <= 64'd0;
    else begin
      if (operation == SHA512_op_DONE_9)
        H[3] <= 64'((H[3] + d));
      else if (operation == SHA512_op_IDLE_1)
        H[3] <= 64'd7466358040605728719;
      else if (operation == SHA512_op_IDLE_2)
        H[3] <= 64'd10824532655140301501;
      else if (operation == SHA512_op_IDLE_3)
        H[3] <= 64'd11912009170470909681;
      else if (operation == SHA512_op_IDLE_4)
        H[3] <= 64'd1526699215303891257;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      H[4] <= 64'd0;
    else begin
      if (operation == SHA512_op_DONE_9)
        H[4] <= 64'((H[4] + e));
      else if (operation == SHA512_op_IDLE_1)
        H[4] <= 64'd1111592415079452072;
      else if (operation == SHA512_op_IDLE_2)
        H[4] <= 64'd10819967247969091555;
      else if (operation == SHA512_op_IDLE_3)
        H[4] <= 64'd5840696475078001361;
      else if (operation == SHA512_op_IDLE_4)
        H[4] <= 64'd7436329637833083697;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      H[5] <= 64'd0;
    else begin
      if (operation == SHA512_op_DONE_9)
        H[5] <= 64'((H[5] + f));
      else if (operation == SHA512_op_IDLE_1)
        H[5] <= 64'd8638871050018654530;
      else if (operation == SHA512_op_IDLE_2)
        H[5] <= 64'd13717434660681038226;
      else if (operation == SHA512_op_IDLE_3)
        H[5] <= 64'd11170449401992604703;
      else if (operation == SHA512_op_IDLE_4)
        H[5] <= 64'd10282925794625328401;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      H[6] <= 64'd0;
    else begin
      if (operation == SHA512_op_DONE_9)
        H[6] <= 64'((H[6] + g));
      else if (operation == SHA512_op_IDLE_1)
        H[6] <= 64'd4583966954114332360;
      else if (operation == SHA512_op_IDLE_2)
        H[6] <= 64'd3098927326965381290;
      else if (operation == SHA512_op_IDLE_3)
        H[6] <= 64'd2270897969802886507;
      else if (operation == SHA512_op_IDLE_4)
        H[6] <= 64'd15784041429090275239;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      H[7] <= 64'd0;
    else begin
      if (operation == SHA512_op_DONE_9)
        H[7] <= 64'((H[7] + h));
      else if (operation == SHA512_op_IDLE_1)
        H[7] <= 64'd1230299281376055969;
      else if (operation == SHA512_op_IDLE_2)
        H[7] <= 64'd1060366662362279074;
      else if (operation == SHA512_op_IDLE_3)
        H[7] <= 64'd6620516959819538809;
      else if (operation == SHA512_op_IDLE_4)
        H[7] <= 64'd5167115440072839076;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      W[0] <= 64'd0;
    else begin
      if (operation == SHA512_op_IDLE_1 || operation == SHA512_op_IDLE_2 || operation == SHA512_op_IDLE_3 || operation == SHA512_op_IDLE_4 || operation == SHA512_op_IDLE_5)
        W[0] <= slicer(SHA_Input_sig.in, 15);
      else if (operation == SHA512_op_SHARounds_8 || operation == SHA512_op_SHARounds_7)
        W[0] <= W[1];
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      W[1] <= 64'd0;
    else begin
      if (operation == SHA512_op_IDLE_1 || operation == SHA512_op_IDLE_2 || operation == SHA512_op_IDLE_3 || operation == SHA512_op_IDLE_4 || operation == SHA512_op_IDLE_5)
        W[1] <= slicer(SHA_Input_sig.in, 14);
      else if (operation == SHA512_op_SHARounds_8 || operation == SHA512_op_SHARounds_7)
        W[1] <= W[2];
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      W[10] <= 64'd0;
    else begin
      if (operation == SHA512_op_IDLE_1 || operation == SHA512_op_IDLE_2 || operation == SHA512_op_IDLE_3 || operation == SHA512_op_IDLE_4 || operation == SHA512_op_IDLE_5)
        W[10] <= slicer(SHA_Input_sig.in, 5);
      else if (operation == SHA512_op_SHARounds_8 || operation == SHA512_op_SHARounds_7)
        W[10] <= W[11];
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      W[11] <= 64'd0;
    else begin
      if (operation == SHA512_op_IDLE_1 || operation == SHA512_op_IDLE_2 || operation == SHA512_op_IDLE_3 || operation == SHA512_op_IDLE_4 || operation == SHA512_op_IDLE_5)
        W[11] <= slicer(SHA_Input_sig.in, 4);
      else if (operation == SHA512_op_SHARounds_8 || operation == SHA512_op_SHARounds_7)
        W[11] <= W[12];
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      W[12] <= 64'd0;
    else begin
      if (operation == SHA512_op_IDLE_1 || operation == SHA512_op_IDLE_2 || operation == SHA512_op_IDLE_3 || operation == SHA512_op_IDLE_4 || operation == SHA512_op_IDLE_5)
        W[12] <= slicer(SHA_Input_sig.in, 3);
      else if (operation == SHA512_op_SHARounds_8 || operation == SHA512_op_SHARounds_7)
        W[12] <= W[13];
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      W[13] <= 64'd0;
    else begin
      if (operation == SHA512_op_IDLE_1 || operation == SHA512_op_IDLE_2 || operation == SHA512_op_IDLE_3 || operation == SHA512_op_IDLE_4 || operation == SHA512_op_IDLE_5)
        W[13] <= slicer(SHA_Input_sig.in, 2);
      else if (operation == SHA512_op_SHARounds_8 || operation == SHA512_op_SHARounds_7)
        W[13] <= W[14];
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      W[14] <= 64'd0;
    else begin
      if (operation == SHA512_op_IDLE_1 || operation == SHA512_op_IDLE_2 || operation == SHA512_op_IDLE_3 || operation == SHA512_op_IDLE_4 || operation == SHA512_op_IDLE_5)
        W[14] <= slicer(SHA_Input_sig.in, 1);
      else if (operation == SHA512_op_SHARounds_8 || operation == SHA512_op_SHARounds_7)
        W[14] <= W[15];
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      W[15] <= 64'd0;
    else begin
      if (operation == SHA512_op_IDLE_1 || operation == SHA512_op_IDLE_2 || operation == SHA512_op_IDLE_3 || operation == SHA512_op_IDLE_4 || operation == SHA512_op_IDLE_5)
        W[15] <= slicer(SHA_Input_sig.in, 0);
      else if (operation == SHA512_op_SHARounds_8 || operation == SHA512_op_SHARounds_7)
        W[15] <= compute_w(W[14], W[9], W[1], W[0]);
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      W[2] <= 64'd0;
    else begin
      if (operation == SHA512_op_IDLE_1 || operation == SHA512_op_IDLE_2 || operation == SHA512_op_IDLE_3 || operation == SHA512_op_IDLE_4 || operation == SHA512_op_IDLE_5)
        W[2] <= slicer(SHA_Input_sig.in, 13);
      else if (operation == SHA512_op_SHARounds_8 || operation == SHA512_op_SHARounds_7)
        W[2] <= W[3];
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      W[3] <= 64'd0;
    else begin
      if (operation == SHA512_op_IDLE_1 || operation == SHA512_op_IDLE_2 || operation == SHA512_op_IDLE_3 || operation == SHA512_op_IDLE_4 || operation == SHA512_op_IDLE_5)
        W[3] <= slicer(SHA_Input_sig.in, 12);
      else if (operation == SHA512_op_SHARounds_8 || operation == SHA512_op_SHARounds_7)
        W[3] <= W[4];
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      W[4] <= 64'd0;
    else begin
      if (operation == SHA512_op_IDLE_1 || operation == SHA512_op_IDLE_2 || operation == SHA512_op_IDLE_3 || operation == SHA512_op_IDLE_4 || operation == SHA512_op_IDLE_5)
        W[4] <= slicer(SHA_Input_sig.in, 11);
      else if (operation == SHA512_op_SHARounds_8 || operation == SHA512_op_SHARounds_7)
        W[4] <= W[5];
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      W[5] <= 64'd0;
    else begin
      if (operation == SHA512_op_IDLE_1 || operation == SHA512_op_IDLE_2 || operation == SHA512_op_IDLE_3 || operation == SHA512_op_IDLE_4 || operation == SHA512_op_IDLE_5)
        W[5] <= slicer(SHA_Input_sig.in, 10);
      else if (operation == SHA512_op_SHARounds_8 || operation == SHA512_op_SHARounds_7)
        W[5] <= W[6];
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      W[6] <= 64'd0;
    else begin
      if (operation == SHA512_op_IDLE_1 || operation == SHA512_op_IDLE_2 || operation == SHA512_op_IDLE_3 || operation == SHA512_op_IDLE_4 || operation == SHA512_op_IDLE_5)
        W[6] <= slicer(SHA_Input_sig.in, 9);
      else if (operation == SHA512_op_SHARounds_8 || operation == SHA512_op_SHARounds_7)
        W[6] <= W[7];
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      W[7] <= 64'd0;
    else begin
      if (operation == SHA512_op_IDLE_1 || operation == SHA512_op_IDLE_2 || operation == SHA512_op_IDLE_3 || operation == SHA512_op_IDLE_4 || operation == SHA512_op_IDLE_5)
        W[7] <= slicer(SHA_Input_sig.in, 8);
      else if (operation == SHA512_op_SHARounds_8 || operation == SHA512_op_SHARounds_7)
        W[7] <= W[8];
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      W[8] <= 64'd0;
    else begin
      if (operation == SHA512_op_IDLE_1 || operation == SHA512_op_IDLE_2 || operation == SHA512_op_IDLE_3 || operation == SHA512_op_IDLE_4 || operation == SHA512_op_IDLE_5)
        W[8] <= slicer(SHA_Input_sig.in, 7);
      else if (operation == SHA512_op_SHARounds_8 || operation == SHA512_op_SHARounds_7)
        W[8] <= W[9];
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      W[9] <= 64'd0;
    else begin
      if (operation == SHA512_op_IDLE_1 || operation == SHA512_op_IDLE_2 || operation == SHA512_op_IDLE_3 || operation == SHA512_op_IDLE_4 || operation == SHA512_op_IDLE_5)
        W[9] <= slicer(SHA_Input_sig.in, 6);
      else if (operation == SHA512_op_SHARounds_8 || operation == SHA512_op_SHARounds_7)
        W[9] <= W[10];
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      a <= 64'd0;
    else begin
      if (operation == SHA512_op_IDLE_1)
        a <= 64'd10105294471447203234;
      else if (operation == SHA512_op_IDLE_2)
        a <= 64'd2463787394917988140;
      else if (operation == SHA512_op_IDLE_3)
        a <= 64'd7640891576956012808;
      else if (operation == SHA512_op_IDLE_4)
        a <= 64'd14680500436340154072;
      else if (operation == SHA512_op_IDLE_5)
        a <= H[0];
      else if (operation == SHA512_op_SHARounds_8)
        a <= 64'((T1(e, f, g, h, 64'd7801388544844847127, compute_w(W[14], W[9], W[1], W[0])) + T2(a, b, c)));
      else if (operation == SHA512_op_SHARounds_6)
        a <= 64'((T1(e, f, g, h, ((i == 0) ? 64'd4794697086780616226 : ((i == 1) ? 64'd8158064640168781261 : ((i == 2) ? 64'd13096744586834688815 : ((i == 3) ? 64'd16840607885511220156 : ((i == 4) ? 64'd4131703408338449720 : ((i == 5) ? 64'd6480981068601479193 : ((i == 6) ? 64'd10538285296894168987 : ((i == 7) ? 64'd12329834152419229976 : ((i == 8) ? 64'd15566598209576043074 : ((i == 9) ? 64'd1334009975649890238 : ((i == 10) ? 64'd2608012711638119052 : ((i == 11) ? 64'd6128411473006802146 : ((i == 12) ? 64'd8268148722764581231 : ((i == 13) ? 64'd9286055187155687089 : ((i == 14) ? 64'd11230858885718282805 : ((i == 15) ? 64'd13951009754708518548 : 64'd7801388544844847127)))))))))))))))), ((i == 0) ? W[0] : ((i == 1) ? W[1] : ((i == 2) ? W[2] : ((i == 3) ? W[3] : ((i == 4) ? W[4] : ((i == 5) ? W[5] : ((i == 6) ? W[6] : ((i == 7) ? W[7] : ((i == 8) ? W[8] : ((i == 9) ? W[9] : ((i == 10) ? W[10] : ((i == 11) ? W[11] : ((i == 12) ? W[12] : ((i == 13) ? W[13] : ((i == 14) ? W[14] : W[15])))))))))))))))) + T2(a, b, c)));
      else if (operation == SHA512_op_SHARounds_7)
        a <= 64'((T1(e, f, g, h, ((i == 16) ? 64'd16472876342353939154 : ((i == 17) ? 64'd17275323862435702243 : ((i == 18) ? 64'd1135362057144423861 : ((i == 19) ? 64'd2597628984639134821 : ((i == 20) ? 64'd3308224258029322869 : ((i == 21) ? 64'd5365058923640841347 : ((i == 22) ? 64'd6679025012923562964 : ((i == 23) ? 64'd8573033837759648693 : ((i == 24) ? 64'd10970295158949994411 : ((i == 25) ? 64'd12119686244451234320 : ((i == 26) ? 64'd12683024718118986047 : ((i == 27) ? 64'd13788192230050041572 : ((i == 28) ? 64'd14330467153632333762 : ((i == 29) ? 64'd15395433587784984357 : ((i == 30) ? 64'd489312712824947311 : ((i == 31) ? 64'd1452737877330783856 : ((i == 32) ? 64'd2861767655752347644 : ((i == 33) ? 64'd3322285676063803686 : ((i == 34) ? 64'd5560940570517711597 : ((i == 35) ? 64'd5996557281743188959 : ((i == 36) ? 64'd7280758554555802590 : ((i == 37) ? 64'd8532644243296465576 : ((i == 38) ? 64'd9350256976987008742 : ((i == 39) ? 64'd10552545826968843579 : ((i == 40) ? 64'd11727347734174303076 : ((i == 41) ? 64'd12113106623233404929 : ((i == 42) ? 64'd14000437183269869457 : ((i == 43) ? 64'd14369950271660146224 : ((i == 44) ? 64'd15101387698204529176 : ((i == 45) ? 64'd15463397548674623760 : ((i == 46) ? 64'd17586052441742319658 : ((i == 47) ? 64'd1182934255886127544 : ((i == 48) ? 64'd1847814050463011016 : ((i == 49) ? 64'd2177327727835720531 : ((i == 50) ? 64'd2830643537854262169 : ((i == 51) ? 64'd3796741975233480872 : ((i == 52) ? 64'd4115178125766777443 : ((i == 53) ? 64'd5681478168544905931 : ((i == 54) ? 64'd6601373596472566643 : ((i == 55) ? 64'd7507060721942968483 : ((i == 56) ? 64'd8399075790359081724 : ((i == 57) ? 64'd8693463985226723168 : ((i == 58) ? 64'd9568029438360202098 : ((i == 59) ? 64'd10144078919501101548 : ((i == 60) ? 64'd10430055236837252648 : ((i == 61) ? 64'd11840083180663258601 : ((i == 62) ? 64'd13761210420658862357 : ((i == 63) ? 64'd14299343276471374635 : ((i == 64) ? 64'd14566680578165727644 : ((i == 65) ? 64'd15097957966210449927 : ((i == 66) ? 64'd16922976911328602910 : ((i == 67) ? 64'd17689382322260857208 : ((i == 68) ? 64'd500013540394364858 : ((i == 69) ? 64'd748580250866718886 : ((i == 70) ? 64'd1242879168328830382 : ((i == 71) ? 64'd1977374033974150939 : ((i == 72) ? 64'd2944078676154940804 : ((i == 73) ? 64'd3659926193048069267 : ((i == 74) ? 64'd4368137639120453308 : ((i == 75) ? 64'd4836135668995329356 : ((i == 76) ? 64'd5532061633213252278 : ((i == 77) ? 64'd6448918945643986474 : ((i == 78) ? 64'd6902733635092675308 : 64'd7801388544844847127))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), compute_w(W[14], W[9], W[1], W[0])) + T2(a, b, c)));
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      b <= 64'd0;
    else begin
      if (operation == SHA512_op_IDLE_1)
        b <= 64'd8350123849800275158;
      else if (operation == SHA512_op_IDLE_2)
        b <= 64'd11481187982095705282;
      else if (operation == SHA512_op_IDLE_3)
        b <= 64'd13503953896175478587;
      else if (operation == SHA512_op_IDLE_4)
        b <= 64'd7105036623409894663;
      else if (operation == SHA512_op_IDLE_5)
        b <= H[1];
      else if (operation == SHA512_op_SHARounds_8 || operation == SHA512_op_SHARounds_6 || operation == SHA512_op_SHARounds_7)
        b <= a;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      c <= 64'd0;
    else begin
      if (operation == SHA512_op_IDLE_1)
        c <= 64'd2160240930085379202;
      else if (operation == SHA512_op_IDLE_2)
        c <= 64'd2563595384472711505;
      else if (operation == SHA512_op_IDLE_3)
        c <= 64'd4354685564936845355;
      else if (operation == SHA512_op_IDLE_4)
        c <= 64'd10473403895298186519;
      else if (operation == SHA512_op_IDLE_5)
        c <= H[2];
      else if (operation == SHA512_op_SHARounds_8 || operation == SHA512_op_SHARounds_6 || operation == SHA512_op_SHARounds_7)
        c <= b;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      d <= 64'd0;
    else begin
      if (operation == SHA512_op_IDLE_1)
        d <= 64'd7466358040605728719;
      else if (operation == SHA512_op_IDLE_2)
        d <= 64'd10824532655140301501;
      else if (operation == SHA512_op_IDLE_3)
        d <= 64'd11912009170470909681;
      else if (operation == SHA512_op_IDLE_4)
        d <= 64'd1526699215303891257;
      else if (operation == SHA512_op_IDLE_5)
        d <= H[3];
      else if (operation == SHA512_op_SHARounds_8 || operation == SHA512_op_SHARounds_6 || operation == SHA512_op_SHARounds_7)
        d <= c;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      e <= 64'd0;
    else begin
      if (operation == SHA512_op_IDLE_1)
        e <= 64'd1111592415079452072;
      else if (operation == SHA512_op_IDLE_2)
        e <= 64'd10819967247969091555;
      else if (operation == SHA512_op_IDLE_3)
        e <= 64'd5840696475078001361;
      else if (operation == SHA512_op_IDLE_4)
        e <= 64'd7436329637833083697;
      else if (operation == SHA512_op_IDLE_5)
        e <= H[4];
      else if (operation == SHA512_op_SHARounds_8)
        e <= 64'((d + T1(e, f, g, h, 64'd7801388544844847127, compute_w(W[14], W[9], W[1], W[0]))));
      else if (operation == SHA512_op_SHARounds_6)
        e <= 64'((d + T1(e, f, g, h, ((i == 0) ? 64'd4794697086780616226 : ((i == 1) ? 64'd8158064640168781261 : ((i == 2) ? 64'd13096744586834688815 : ((i == 3) ? 64'd16840607885511220156 : ((i == 4) ? 64'd4131703408338449720 : ((i == 5) ? 64'd6480981068601479193 : ((i == 6) ? 64'd10538285296894168987 : ((i == 7) ? 64'd12329834152419229976 : ((i == 8) ? 64'd15566598209576043074 : ((i == 9) ? 64'd1334009975649890238 : ((i == 10) ? 64'd2608012711638119052 : ((i == 11) ? 64'd6128411473006802146 : ((i == 12) ? 64'd8268148722764581231 : ((i == 13) ? 64'd9286055187155687089 : ((i == 14) ? 64'd11230858885718282805 : ((i == 15) ? 64'd13951009754708518548 : 64'd7801388544844847127)))))))))))))))), ((i == 0) ? W[0] : ((i == 1) ? W[1] : ((i == 2) ? W[2] : ((i == 3) ? W[3] : ((i == 4) ? W[4] : ((i == 5) ? W[5] : ((i == 6) ? W[6] : ((i == 7) ? W[7] : ((i == 8) ? W[8] : ((i == 9) ? W[9] : ((i == 10) ? W[10] : ((i == 11) ? W[11] : ((i == 12) ? W[12] : ((i == 13) ? W[13] : ((i == 14) ? W[14] : W[15]))))))))))))))))));
      else if (operation == SHA512_op_SHARounds_7)
        e <= 64'((d + T1(e, f, g, h, ((i == 16) ? 64'd16472876342353939154 : ((i == 17) ? 64'd17275323862435702243 : ((i == 18) ? 64'd1135362057144423861 : ((i == 19) ? 64'd2597628984639134821 : ((i == 20) ? 64'd3308224258029322869 : ((i == 21) ? 64'd5365058923640841347 : ((i == 22) ? 64'd6679025012923562964 : ((i == 23) ? 64'd8573033837759648693 : ((i == 24) ? 64'd10970295158949994411 : ((i == 25) ? 64'd12119686244451234320 : ((i == 26) ? 64'd12683024718118986047 : ((i == 27) ? 64'd13788192230050041572 : ((i == 28) ? 64'd14330467153632333762 : ((i == 29) ? 64'd15395433587784984357 : ((i == 30) ? 64'd489312712824947311 : ((i == 31) ? 64'd1452737877330783856 : ((i == 32) ? 64'd2861767655752347644 : ((i == 33) ? 64'd3322285676063803686 : ((i == 34) ? 64'd5560940570517711597 : ((i == 35) ? 64'd5996557281743188959 : ((i == 36) ? 64'd7280758554555802590 : ((i == 37) ? 64'd8532644243296465576 : ((i == 38) ? 64'd9350256976987008742 : ((i == 39) ? 64'd10552545826968843579 : ((i == 40) ? 64'd11727347734174303076 : ((i == 41) ? 64'd12113106623233404929 : ((i == 42) ? 64'd14000437183269869457 : ((i == 43) ? 64'd14369950271660146224 : ((i == 44) ? 64'd15101387698204529176 : ((i == 45) ? 64'd15463397548674623760 : ((i == 46) ? 64'd17586052441742319658 : ((i == 47) ? 64'd1182934255886127544 : ((i == 48) ? 64'd1847814050463011016 : ((i == 49) ? 64'd2177327727835720531 : ((i == 50) ? 64'd2830643537854262169 : ((i == 51) ? 64'd3796741975233480872 : ((i == 52) ? 64'd4115178125766777443 : ((i == 53) ? 64'd5681478168544905931 : ((i == 54) ? 64'd6601373596472566643 : ((i == 55) ? 64'd7507060721942968483 : ((i == 56) ? 64'd8399075790359081724 : ((i == 57) ? 64'd8693463985226723168 : ((i == 58) ? 64'd9568029438360202098 : ((i == 59) ? 64'd10144078919501101548 : ((i == 60) ? 64'd10430055236837252648 : ((i == 61) ? 64'd11840083180663258601 : ((i == 62) ? 64'd13761210420658862357 : ((i == 63) ? 64'd14299343276471374635 : ((i == 64) ? 64'd14566680578165727644 : ((i == 65) ? 64'd15097957966210449927 : ((i == 66) ? 64'd16922976911328602910 : ((i == 67) ? 64'd17689382322260857208 : ((i == 68) ? 64'd500013540394364858 : ((i == 69) ? 64'd748580250866718886 : ((i == 70) ? 64'd1242879168328830382 : ((i == 71) ? 64'd1977374033974150939 : ((i == 72) ? 64'd2944078676154940804 : ((i == 73) ? 64'd3659926193048069267 : ((i == 74) ? 64'd4368137639120453308 : ((i == 75) ? 64'd4836135668995329356 : ((i == 76) ? 64'd5532061633213252278 : ((i == 77) ? 64'd6448918945643986474 : ((i == 78) ? 64'd6902733635092675308 : 64'd7801388544844847127))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))), compute_w(W[14], W[9], W[1], W[0]))));
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      f <= 64'd0;
    else begin
      if (operation == SHA512_op_IDLE_1)
        f <= 64'd8638871050018654530;
      else if (operation == SHA512_op_IDLE_2)
        f <= 64'd13717434660681038226;
      else if (operation == SHA512_op_IDLE_3)
        f <= 64'd11170449401992604703;
      else if (operation == SHA512_op_IDLE_4)
        f <= 64'd10282925794625328401;
      else if (operation == SHA512_op_IDLE_5)
        f <= H[5];
      else if (operation == SHA512_op_SHARounds_8 || operation == SHA512_op_SHARounds_6 || operation == SHA512_op_SHARounds_7)
        f <= e;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      g <= 64'd0;
    else begin
      if (operation == SHA512_op_IDLE_1)
        g <= 64'd4583966954114332360;
      else if (operation == SHA512_op_IDLE_2)
        g <= 64'd3098927326965381290;
      else if (operation == SHA512_op_IDLE_3)
        g <= 64'd2270897969802886507;
      else if (operation == SHA512_op_IDLE_4)
        g <= 64'd15784041429090275239;
      else if (operation == SHA512_op_IDLE_5)
        g <= H[6];
      else if (operation == SHA512_op_SHARounds_8 || operation == SHA512_op_SHARounds_6 || operation == SHA512_op_SHARounds_7)
        g <= f;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      h <= 64'd0;
    else begin
      if (operation == SHA512_op_IDLE_1)
        h <= 64'd1230299281376055969;
      else if (operation == SHA512_op_IDLE_2)
        h <= 64'd1060366662362279074;
      else if (operation == SHA512_op_IDLE_3)
        h <= 64'd6620516959819538809;
      else if (operation == SHA512_op_IDLE_4)
        h <= 64'd5167115440072839076;
      else if (operation == SHA512_op_IDLE_5)
        h <= H[7];
      else if (operation == SHA512_op_SHARounds_8 || operation == SHA512_op_SHARounds_6 || operation == SHA512_op_SHARounds_7)
        h <= g;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      i <= 0;
    else begin
      if (operation == SHA512_op_IDLE_1 || operation == SHA512_op_IDLE_2 || operation == SHA512_op_IDLE_3 || operation == SHA512_op_IDLE_4 || operation == SHA512_op_IDLE_5)
        i <= 0;
      else if (operation == SHA512_op_SHARounds_8 || operation == SHA512_op_SHARounds_6 || operation == SHA512_op_SHARounds_7)
        i <= (1 + i);
    end
  end

  always_ff @(posedge clk) begin
    if (operation == SHA512_op_DONE_9)
      out_sig <= 512'(((512'(((512'(((512'(((512'(((512'(((512'((((64'((H[7] + h)) << 64'd448) >> 512'd64) + (64'((H[6] + g)) << 64'd448))) >> 512'd64) + (64'((H[5] + f)) << 64'd448))) >> 512'd64) + (64'((H[4] + e)) << 64'd448))) >> 512'd64) + (64'((H[3] + d)) << 64'd448))) >> 512'd64) + (64'((H[2] + c)) << 64'd448))) >> 512'd64) + (64'((H[1] + b)) << 64'd448))) >> 512'd64) + (64'((H[0] + a)) << 64'd448)));
  end

  always_ff @(posedge clk) begin
    if (rst)
      SHA_Input_notify <= 1;
    else begin
      if (operation == SHA512_op_DONE_9 || operation == SHA512_op_wait_IDLE)
        SHA_Input_notify <= 1;
      else if (operation == SHA512_op_IDLE_1 || operation == SHA512_op_IDLE_2 || operation == SHA512_op_IDLE_3 || operation == SHA512_op_IDLE_4 || operation == SHA512_op_IDLE_5 || operation == SHA512_op_SHARounds_8 || operation == SHA512_op_SHARounds_6 || operation == SHA512_op_SHARounds_7)
        SHA_Input_notify <= 0;
    end
  end

  always_ff @(posedge clk) begin
    if (rst)
      out_notify <= 0;
    else begin
      if (operation == SHA512_op_DONE_9)
        out_notify <= 1;
      else if (operation == SHA512_op_IDLE_1 || operation == SHA512_op_IDLE_2 || operation == SHA512_op_IDLE_3 || operation == SHA512_op_IDLE_4 || operation == SHA512_op_IDLE_5 || operation == SHA512_op_SHARounds_8 || operation == SHA512_op_SHARounds_6 || operation == SHA512_op_SHARounds_7)
        out_notify <= 0;
    end
  end

  assign i_out = i;

endmodule
