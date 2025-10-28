module gqed
#(
parameter SEQ_LEN = 64,
parameter RESP_BOUND = 34,
parameter BOUND_OPLEN = 16
)
(
input clk, rst,
input [24:0] in [0:SEQ_LEN-1],
input [7:0] xram_in [0:BOUND_OPLEN-1],
input [$clog2(SEQ_LEN)-1:0] i, j,
input [15:0] bmc_addr,
input [24:0] bmc_in2, bmc_in3,
input in_vld2 
);

reg [7:0] bound;
wire [7:0] bound3 = j==0?0:RESP_BOUND; 

STABLE: assume property (@(posedge clk) $stable(in) && $stable(i) && $stable(xram_in) && in[i][23:8]<16'hff30 && in[i][23:8]>=16'hff00 && $stable(j) && j<SEQ_LEN-RESP_BOUND-1);

ONE_OUTPUT_i_READ: assume property (@(posedge clk) in[i][24] |-> !in[i+1][24] || (in[i+1][23:8]==16'hff00 && in[i+1][0]));
ONE_OUTPUT_i_START: assume property (@(posedge clk) in[i][23:8]==16'hff00 && in[i][0] && in[i][24] |-> !in[i+1][24] || in[i+1][23:8]!=16'hff00 || !in[i+1][0]);

reg [$clog2(SEQ_LEN)-1:0] cntr1, cntr2, no_ocntr2, cntr3, ocntr;

reg [15:0] arch_st_addr1, arch_st_len1;
reg [127:0] arch_st_key1, arch_st_ctr1;
reg [15:0] arch_st_addr3, arch_st_len3;
reg [127:0] arch_st_key3, arch_st_ctr3;
reg [1:0] arch_st_aes_st1;
reg [1:0] arch_st_aes_st3;

reg [7:0] xram_out2 [0:BOUND_OPLEN-1];
reg [7:0] xram_out3 [0:BOUND_OPLEN-1];

reg [15:0] addr2 [0:2*BOUND_OPLEN-1];
reg [15:0] xram_addr3 [0:2*BOUND_OPLEN-1];

reg [$clog2(BOUND_OPLEN)-1:0] xram_cntr2, xram_ocntr2, xram_cntr3, xram_ocntr3; 
reg [$clog2(2*BOUND_OPLEN)-1:0] addr_cntr2, addr_cntr3; 

wire ack1, ack2, ack3, xram_ack1, xram_ack2, xram_ack3, xram_stb1, xram_stb2, xram_stb3, xram_wr2, xram_wr3; 

reg arch_st_done1, arch_st_done3;

wire [7:0] out2, out3, xram_out2_w, xram_out3_w;
wire [15:0] addr2_w, addr3_w;

reg i_op_start2, i_op_start3;

reg [7:0] cmp_out2, cmp_out3;

wire [1:0] st1, st2, st3, wr3;
wire [15:0] addr3;
wire [7:0] data3;
assign {wr3, addr3, data3} = cntr3==j+bound3? in[i]:cntr3==j+bound3+1?in[i+1]:bmc_in3;

aes_top copy1 ( .clk(clk), .rst(rst), .wr(in[cntr1][24]), .addr(cntr1<i?in[cntr1][23:8]:bmc_addr), .data_in(in[cntr1][7:0]), .data_out(out1), .ack(ack1), .stb(1'b1), .xram_ack(xram_ack1), .xram_stb(xram_stb1), .aes_state(st1));
aes_top copy2 ( .clk(clk), .rst(rst), .wr(cntr2<=i+1 && in_vld2?in[cntr2][24]:bmc_in2[24]), .addr(cntr2<=i+1 && in_vld2?in[cntr2][23:8]:bmc_in2[23:8]), .data_in(cntr2<=i+1 && in_vld2?in[cntr2][7:0]:bmc_in2[7:0]), .data_out(out2), .ack(ack2), .stb(1'b1), .xram_addr(addr2_w), .xram_data_out(xram_out2_w), .xram_data_in(xram_in[xram_cntr2]), .xram_ack(xram_ack2), .xram_stb(xram_stb2), .xram_wr(xram_wr2), .aes_state(st2));
aes_top copy3 ( .clk(clk), .rst(rst), .wr(wr3), .addr(addr3), .data_in(data3), .data_out(out3), .ack(ack3), .stb(1'b1), .xram_addr(addr3_w), .xram_data_out(xram_out3_w), .xram_data_in(xram_in[xram_cntr3]), .xram_ack(xram_ack3), .xram_stb(xram_stb3), .xram_wr(xram_wr3), .aes_state(st3));

LEGAL1: assume property (@(posedge clk) !xram_stb1 == !xram_ack1);
LEGAL2: assume property (@(posedge clk) !xram_stb2 |-> !xram_ack2);
LEGAL3: assume property (@(posedge clk) !xram_stb3 == !xram_ack3);
LEGAL4: assume property (@(posedge clk) st1!=2'b00 |-> !copy1.wr && ((copy1.addr>=16'hff02 && copy1.addr<16'hff10) || (copy1.addr<16'hff00 || copy1.addr>=16'hff30)));   
LEGAL5: assume property (@(posedge clk) st2!=2'b00 |-> !copy2.wr && ((copy2.addr>=16'hff02 && copy2.addr<16'hff10) || (copy2.addr<16'hff00 || copy2.addr>=16'hff30)));   
LEGAL6: assume property (@(posedge clk) st3!=2'b00 |-> !copy3.wr && ((copy3.addr>=16'hff02 && copy3.addr<16'hff10) || (copy3.addr<16'hff00 || copy3.addr>=16'hff30)));   

SAME_ARCH_AT_RST: assume property (@(posedge clk) $fell(rst) |-> copy1.aes_reg_state == copy2.aes_reg_state && copy1.aes_reg_opaddr_i.reg_out == copy2.aes_reg_opaddr_i.reg_out && copy1.aes_reg_oplen_i.reg_out == copy2.aes_reg_oplen_i.reg_out && copy1.aes_reg_ctr_i.reg_out == copy2.aes_reg_ctr_i.reg_out && copy1.aes_reg_key0_i.reg_out == copy2.aes_reg_key0_i.reg_out);


always @(posedge clk) begin
	if(rst) begin
		cntr1 <= 'b0;
		cntr2 <= 'b0;
		no_ocntr2 <= 'b0;
		cntr3 <= 'b0;
		bound <= 'b0;
		arch_st_done3 <= 1'b0;
		arch_st_done1 <= 1'b0;
		i_op_start2 <= 1'b0;
		i_op_start3 <= 1'b0;
	end else begin 
		if (ack1 && cntr1<i) begin
			cntr1 <= cntr1 + 'b1; 
		end if (ack2) begin
			if (in_vld2 && cntr2<=i+1)
				cntr2 <= cntr2 + 'b1;
			if (in_vld2 && in[cntr2][24] && cntr2<=i+1)
				no_ocntr2 <= no_ocntr2 + 'b1;
			if (in_vld2 && (cntr2==i || cntr2==i+1) && in[cntr2][23:8]==16'hff00 && in[cntr2][24] && in[cntr2][0])
				i_op_start2 <= 1'b1; 
		end 
		if (ack3 && cntr3<j+bound3+2) begin
			cntr3 <= cntr3 + 'b1;
			if(cntr3==j+bound3) begin
				arch_st_addr3 <= copy3.aes_reg_opaddr_i.reg_out;
				arch_st_len3 <= copy3.aes_reg_oplen_i.reg_out;
				arch_st_key3 <= copy3.aes_reg_key0_i.reg_out;
				arch_st_ctr3 <= copy3.aes_reg_ctr_i.reg_out;
				arch_st_aes_st3 <= copy3.aes_reg_state;
				arch_st_done3 <= 1'b1;
			end if(cntr3>=j+bound3 && in[i+cntr3-j-bound3][23:8]==16'hff00 && in[i+cntr3-j-bound3][24] && in[i+cntr3-j-bound3][0])
				i_op_start3 <= 1'b1;						
		end if (cntr1 == i && bound < RESP_BOUND-1 && i>0)
			bound <= bound + 'b1;			
		if (bound == (i==0?0:RESP_BOUND-1)) begin
			arch_st_addr1 <= copy1.aes_reg_opaddr_i.reg_out;
			arch_st_len1 <= copy1.aes_reg_oplen_i.reg_out;
			arch_st_key1 <= copy1.aes_reg_key0_i.reg_out;
			arch_st_ctr1 <= copy1.aes_reg_ctr_i.reg_out;
			arch_st_aes_st1 <= copy1.aes_reg_state;
			arch_st_done1 <= 1'b1;									
		end				
	end
end

CPY3_STABLE_ST: assume property (@(posedge clk) (cntr3>j && cntr3<j+bound3) || cntr3>j+bound3+1 |-> bmc_in3[23:8]<16'hff00 || bmc_in3[23:8]>=16'hff30);   
LEGAL7: assume property (@(posedge clk) bmc_addr<16'hff00 || bmc_addr>=16'hff30);
LEGAL8: assume property (@(posedge clk) !in_vld2 |-> bmc_in2[23:8]<16'hff00 || bmc_in2[23:8]>=16'hff30);
LEGAL9: assume property (@(posedge clk) arch_st_len1 <= BOUND_OPLEN);

reg done2, done3, xram_done2, xram_done3;
	
reg [2:0] st2_prev, st3_prev;

always @(posedge clk) begin
	if(rst || cntr3<j+bound3) begin
		done3 <= 1'b0;
		st3_prev <= 2'b0;
	end if(rst) begin
		ocntr <= 'b0;
		done2 <= 1'b0;
		st2_prev <= 2'b0;
	end else begin 
		if (!in[cntr2][24] && ack2 && ocntr<=i+1)
			ocntr <= ocntr + 'b1;
		if (cntr3>=j+bound3 && !in[i+cntr3-j-bound3][24] && !done3 && ack3) begin
			cmp_out3 <= out3;
			done3 <= 1'b1;
		end if (!in[cntr2][24] && ocntr == i-no_ocntr2 && ack2) begin
			cmp_out2 <= out2;
			done2 <= 1'b1;
		end 
		st2_prev <= st2;
		st3_prev <= st3;
	end
end 
always_comb begin
	if(rst) begin
		xram_done2 = 1'b0;
		xram_done3 = 1'b0;
	end else begin
		if (i_op_start2 && st2==2'd0 && st2_prev!=2'd0)
			xram_done2 = 1'b1;
		if (i_op_start3 && st3==2'd0 && st3_prev!=2'd0)
			xram_done3 = 1'b1;
	end
end


always @(posedge clk) begin
	if(rst || cntr3<j+bound3) begin
		xram_cntr3 <= 'b0;
		xram_ocntr3 <= 'b0;
		addr_cntr3 <= 'b0;
		xram_out3 <= '{default:0};
		xram_addr3 <= '{default:0};
	end if(rst) begin
		xram_cntr2 <= 'b0;
		xram_ocntr2 <= 'b0; 
		addr_cntr2 <= 'b0;
		xram_out2 <= '{default:0};
		addr2 <= '{default:0};
	end else begin 
		if (i_op_start2 && xram_ack2 && xram_stb2 && !xram_wr2 && !xram_done2)
			xram_cntr2 <= xram_cntr2 + 'b1;
		if (i_op_start2 && xram_ack2 && xram_stb2 && xram_wr2 && !xram_done2) begin
			xram_ocntr2 <= xram_ocntr2 + 'b1;
			xram_out2[xram_ocntr2] <= xram_out2_w;
		end if (i_op_start3 && xram_ack3 && xram_stb3 && !xram_wr3 && !xram_done3)
			xram_cntr3 <= xram_cntr3 + 'b1;
		if (i_op_start3 && xram_ack3 && xram_stb3 && xram_wr3 && !xram_done3) begin
			xram_ocntr3 <= xram_ocntr3 + 'b1;
			xram_out3[xram_ocntr3] <= xram_out3_w;
		end if (i_op_start2 && xram_ack2 && xram_stb2 && !xram_done2) begin
			addr_cntr2 <= addr_cntr2 + 'b1;
			addr2[addr_cntr2] <= addr2_w;
		end if (i_op_start3 && xram_ack3 && xram_stb3 && !xram_done3) begin
			addr_cntr3 <= addr_cntr3 + 'b1;
			xram_addr3[addr_cntr3] <= addr3_w;
		end
	end
end


SAME_ARCH_i_START: assume property (@(posedge clk) (arch_st_done1 && arch_st_done3 && in[i][23:8]==16'hff00 && in[i][24] && in[i][0]) |-> arch_st_aes_st1 == arch_st_aes_st3 && arch_st_addr1==arch_st_addr3 && arch_st_len1==arch_st_len3 && arch_st_key1==arch_st_key3 && arch_st_ctr1==arch_st_ctr3);
SAME_ARCH_i_READ_STATE: assume property (@(posedge clk) (arch_st_done1 && arch_st_done3 && in[i][23:8]==16'hff01 && !in[i][24]) |-> arch_st_aes_st1 == arch_st_aes_st3);
SAME_ARCH_i_READ_ADDR: assume property (@(posedge clk) (arch_st_done1 && arch_st_done3 && in[i][23:8]>=16'hff02 && in[i][23:8]<16'hff04 && !in[i][24]) |-> arch_st_addr1==arch_st_addr3);
SAME_ARCH_i_READ_OPLEN: assume property (@(posedge clk) (arch_st_done1 && arch_st_done3 && in[i][23:8]>=16'hff04 && in[i][23:8]<16'hff10 && !in[i][24]) |-> arch_st_len1==arch_st_len3);
SAME_ARCH_i_READ_KEY: assume property (@(posedge clk) (arch_st_done1 && arch_st_done3 && in[i][23:8]>=16'hff10 && in[i][23:8]<16'hff20 && !in[i][24]) |-> arch_st_key1==arch_st_key3);
SAME_ARCH_i_READ_CTR: assume property (@(posedge clk) (arch_st_done1 && arch_st_done3 && in[i][23:8]>=16'hff20 && in[i][23:8]<16'hff30 && !in[i][24]) |-> arch_st_ctr1==arch_st_ctr3);

SAME_ARCH_iplus1_START: assume property (@(posedge clk) (arch_st_done1 && arch_st_done3 && in[i+1][23:8]==16'hff00 && in[i+1][24] && in[i+1][0]) |-> arch_st_aes_st1 == arch_st_aes_st3 && arch_st_addr1==arch_st_addr3 && arch_st_len1==arch_st_len3 && arch_st_key1==arch_st_key3 && arch_st_ctr1==arch_st_ctr3);
SAME_ARCH_iplus1_READ_STATE: assume property (@(posedge clk) (arch_st_done1 && arch_st_done3 && in[i+1][23:8]==16'hff01 && !in[i+1][24]) |-> arch_st_aes_st1 == arch_st_aes_st3);
SAME_ARCH_iplus1_READ_ADDR: assume property (@(posedge clk) (arch_st_done1 && arch_st_done3 && in[i+1][23:8]>=16'hff02 && in[i+1][23:8]<16'hff04 && !in[i+1][24]) |-> arch_st_addr1==arch_st_addr3);
SAME_ARCH_iplus1_READ_OPLEN: assume property (@(posedge clk) (arch_st_done1 && arch_st_done3 && in[i+1][23:8]>=16'hff04 && in[i+1][23:8]<16'hff10 && !in[i+1][24]) |-> arch_st_len1==arch_st_len3);
SAME_ARCH_iplus1_READ_KEY: assume property (@(posedge clk) (arch_st_done1 && arch_st_done3 && in[i+1][23:8]>=16'hff10 && in[i+1][23:8]<16'hff20 && !in[i+1][24]) |-> arch_st_key1==arch_st_key3);
SAME_ARCH_iplus1_READ_CTR: assume property (@(posedge clk) (arch_st_done1 && arch_st_done3 && in[i+1][23:8]>=16'hff20 && in[i+1][23:8]<16'hff30 && !in[i+1][24]) |-> arch_st_ctr1==arch_st_ctr3);

FC_8051: assert property (@(posedge clk) done3 && done2 && arch_st_done1 |-> cmp_out3 == cmp_out2);

FC_xaddr: assert property (@(posedge clk) xram_done3 && xram_done2 && arch_st_done1 |-> addr2==xram_addr3);

FC_xdata: assert property (@(posedge clk) xram_done3 && xram_done2 && arch_st_done1 |-> xram_out2==xram_out3);

endmodule 
