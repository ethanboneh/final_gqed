module gqed
#(
parameter SEQ_LEN = 32,
parameter RESP_BOUND = 5
)
(
input clk, rst,
input [2:0] in [0:SEQ_LEN-1],
input [$clog2(SEQ_LEN)-1:0] i, j,
input in_vld2, in_vld3,
input [2:0] bmc_in2, bmc_in3
);


reg [7:0] bound;
wire [7:0] bound3 = j==0?0:RESP_BOUND; 

STABLE: assume property (@(posedge clk) $stable(in) && $stable(i) && $stable(j) && j<SEQ_LEN-RESP_BOUND-1);

reg [$clog2(SEQ_LEN)-1:0] cntr1, cntr2, cntr3, ocntr;

reg [1:0] arch_st1, arch_st3;

wire ovld_cpy1, ovld_cpy2, ovld_cpy3;
reg arch_st_done1, arch_st_done3;

wire [1:0] out2, out3;
wire [1:0] data3;
wire action3;
assign {action3, data3} = cntr3==j+bound3? in[i]:(cntr3==j+bound3+1?in[i+1]:bmc_in3);
			
Pipe copy1 (.clk(clk), .rst(rst), .data(in[cntr1][1:0]), .action(in[cntr1][2]), .in_vld(cntr1<i?1:0));
Pipe copy2 (.clk(clk), .rst(rst), .data(in_vld2 && cntr2<=i+1?in[cntr2][1:0]:bmc_in2[1:0]), .action(in_vld2 && cntr2<=i+1?in[cntr2][2]:bmc_in2[2]), .out(out2), .in_vld(in_vld2), .out_vld(ovld_cpy2));
Pipe copy3 (.clk(clk), .rst(rst), .data(data3), .action(action3), .out(out3), .in_vld(in_vld3), .out_vld(ovld_cpy3));


SAME_ARCH_AT_RST: assume property (@(posedge clk) $fell(rst) |-> copy1.pipe[2][1:0] == copy2.pipe[2][1:0]);


always @(posedge clk) begin
	if(rst) begin
		cntr1 <= 'b0;
		cntr2 <= 'b0;
		cntr3 <= 'b0;
		bound <= 'b0;
		arch_st_done3 <= 1'b0;
		arch_st_done1 <= 1'b0;
	end else begin 
		if (cntr1<i)
			cntr1 <= cntr1 + 'b1;
		if (in_vld2 && cntr2<=i+1)
			cntr2 <= cntr2 + 'b1;
		if (cntr3<j+bound3+2) begin
			cntr3 <= cntr3 + 'b1;
			if(cntr3==j+bound3) begin
				arch_st3 <= copy3.pipe[2][1:0];
				arch_st_done3 <= 1'b1;
			end
		end if (cntr1 == i && bound < RESP_BOUND-1 && i>0)
			bound <= bound + 'b1;			
		if (bound == (i==0?0:RESP_BOUND-1)) begin
			arch_st1 <= copy1.pipe[2][1:0];
			arch_st_done1 <= 1'b1;									
		end				
	end
end


CPY3_STABLE_ST: assume property (@(posedge clk) (cntr3>j && cntr3<j+bound3) || cntr3>j+bound3+1 |-> !in_vld3);   

reg [1:0] cmp_out2 [0:1];
reg [1:0] cmp_out3 [0:1];
reg done2, done3;
reg [1:0] out3_cntr, out2_cntr;

always @(posedge clk) begin
	if(rst || cntr3<j+bound3) begin
		out3_cntr <= 2'b0;
		done3 <= 1'b0;
	end if(rst) begin
		done2 <= 1'b0;
		out2_cntr <= 2'b0;
		ocntr <= 'b0;
	end else begin 
		if (ovld_cpy2 && ocntr<=i+1)
			ocntr <= ocntr + 'b1;
		if (cntr3>=j+bound3 && ovld_cpy3 && !done3) begin
			cmp_out3[out3_cntr] <= out3;
			if(out3_cntr == 2'd1)
				done3 <= 1;
			out3_cntr <= out3_cntr + 1;
		end if (ovld_cpy2 && (ocntr == i || ocntr == i+1) && !done2) begin
			cmp_out2[out2_cntr] <= out2;
			out2_cntr <= out2_cntr + 1;
			if(out2_cntr == 2'd1)
				done2 <= 1;
		end
	end
end

SAME_ARCH: assume property (@(posedge clk) (arch_st_done1 && arch_st_done3) |-> arch_st1==arch_st3);

FC: assert property (@(posedge clk) done3 && done2 && arch_st_done1 |-> cmp_out3 == cmp_out2);

endmodule 
