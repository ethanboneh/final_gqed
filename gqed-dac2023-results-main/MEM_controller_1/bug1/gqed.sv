module gqed
#(
parameter SEQ_LEN = 32,
RESP_BOUND = 2
)
(
input clk, clk_en, tile_en, rst,
input [33:0] in [0:SEQ_LEN-1],
input [$clog2(SEQ_LEN)-1:0] i, j,
input in_vld2,
input [33:0] bmc_in2, bmc_in3
);

reg [7:0] bound;
wire [7:0] bound3 = j==0?0:RESP_BOUND;
 
STABLE: assume property (@(posedge clk) $stable(in) && $stable(i) && $stable(j) && j<SEQ_LEN-RESP_BOUND-1);
ONE_OUTPUT_i_WRITE: assume property (@(posedge clk) in[i][33] |-> in[i+1][33:32]==2'b1);

reg [$clog2(SEQ_LEN)-1:0] cntr1, cntr2, cntr3, ocntr, no_ocntr2;


reg [15:0] arch_st1_i;
reg [15:0] arch_st3_i;
reg [15:0] arch_st1_i1;
reg [15:0] arch_st3_i1;

reg arch_st_done1, arch_st_done3;

wire [15:0] out2, out3;

wire wen2, ren2, wen3, ren3;
wire [15:0] addr3;
wire [15:0] data3;
assign {wen3, ren3, data3, addr3} = cntr3==j+bound3? in[i]:(cntr3==j+bound3+1?in[i+1]:bmc_in3);

ALL_$in$_VALID: assume property (@(posedge clk) in[cntr1][33:32]!=2'b00 && in[cntr2][33:32]!=2'b00 && in[cntr3][33:32]!=2'b00);

memory_core copy1 (.clk(clk), .clk_en(1'b1), .reset(rst), .flush(1'b0), .config_en_sram(4'b0), .enable_chain(1'b0), .tile_en(1'b1), .addr_in(in[cntr1][15:0]), .data_in(in[cntr1][31:16]), .wen_in(cntr1<i?in[cntr1][33]:1'b0), .ren_in(cntr1<i?in[cntr1][32]:1'b0), .mode(2'd2));
memory_core copy2 (.clk(clk), .clk_en(clk_en), .reset(rst), .flush(1'b0), .config_en_sram(4'b0), .enable_chain(1'b0), .tile_en(tile_en), .addr_in(in_vld2 && cntr2<=i+1?in[cntr2][15:0]:bmc_in2[15:0]), .data_in(in_vld2 && cntr2<=i+1?in[cntr2][31:16]:bmc_in2[31:16]), .wen_in(wen2), .ren_in(ren2), .mode(2'd2), .data_out(out2));
memory_core copy3 (.clk(clk), .clk_en(1'b1), .reset(rst), .flush(1'b0), .config_en_sram(4'b0), .enable_chain(1'b0), .tile_en(1'b1), .addr_in(addr3), .data_in(data3), .wen_in(wen3), .ren_in(ren3), .mode(2'd2), .data_out(out3));

assign wen2 = in_vld2 && cntr2 <= i+1 ? in[cntr2][33] : (cntr2 <= i+1 ? 1'b0 : bmc_in2[33]);
assign ren2 = in_vld2 && cntr2 <= i+1 ? in[cntr2][32] : (cntr2 <= i+1 ? 1'b0 : bmc_in2[32]);

SAME_ARCH_AT_RST: assume property (@(posedge clk) $fell(rst) |-> copy1.mem_inst0.sram_stub.data_array == copy2.mem_inst0.sram_stub.data_array && copy1.mem_inst1.sram_stub.data_array == copy2.mem_inst1.sram_stub.data_array);

wire gclk = clk & tile_en;


always @(posedge gclk) begin
	if(rst) begin
		cntr2 <= 'b0;
		no_ocntr2 <= 'b0;
	end else begin 
		if (clk_en && in_vld2 && cntr2<=i+1) begin
			cntr2 <= cntr2 + 'b1;
			if (!in[cntr2][32] || in[cntr2][33])
				no_ocntr2 <= no_ocntr2 + 'b1;
		end 			
	end
end

always @(posedge clk) begin
	if(rst) begin
		cntr1 <= 'b0;
		cntr3 <= 'b0;
		bound <= 'b0;
		arch_st_done3 <= 1'b0;
		arch_st_done1 <= 1'b0;
	end else begin 
		if (cntr1<i)
			cntr1 <= cntr1 + 'b1;
		if (cntr3<j+bound3+2) begin
			cntr3 <= cntr3 + 'b1;
			if(cntr3==j+bound3) begin
				if(in[i][9])
					arch_st3_i <= copy3.mem_inst1.sram_stub.data_array[in[i][8:0]];
				else
					arch_st3_i <= copy3.mem_inst0.sram_stub.data_array[in[i][8:0]];
				if(in[i+1][9])
					arch_st3_i1 <= copy3.mem_inst1.sram_stub.data_array[in[i+1][8:0]];
				else
					arch_st3_i1 <= copy3.mem_inst0.sram_stub.data_array[in[i+1][8:0]];
				arch_st_done3 <= 1'b1;
			end						
		end if (cntr1 == i && bound < RESP_BOUND-1 && i>0)
			bound <= bound + 'b1;			
		if (bound == (i==0?0:RESP_BOUND-1)) begin
			if(in[i][9])
				arch_st1_i <= copy1.mem_inst1.sram_stub.data_array[in[i][8:0]];
			else
				arch_st1_i <= copy1.mem_inst0.sram_stub.data_array[in[i][8:0]];
			if(in[i+1][9])
				arch_st1_i1 <= copy1.mem_inst1.sram_stub.data_array[in[i+1][8:0]];
			else
				arch_st1_i1 <= copy1.mem_inst0.sram_stub.data_array[in[i+1][8:0]];
			arch_st_done1 <= 1'b1;									
		end				
	end
end

assume property (@(posedge clk) (cntr3>j && cntr3<j+bound3) || cntr3>j+bound3+1 |-> !wen3 && !ren3);   


reg [15:0] cmp_out2;
reg [15:0] cmp_out3;
reg done2, done3;

reg ren_d2, ren_d3;

always @(posedge gclk) begin
	if(rst)
		ren_d2 <= 1'b0;
	else if (clk_en)
		ren_d2 <= in_vld2 && (in[cntr2][33:32]==2'b1); 
end

always @(posedge clk) begin
	if(rst || cntr3<j+bound3)
		ren_d3 <= 1'b0;
	else
		ren_d3 <= (in[cntr3-j-bound3+i][33:32]==2'b1); 
end

always @(posedge gclk) begin
	if(rst) begin
		ocntr <= 'b0;
		done2 <= 1'b0;
	end else begin 
		if (clk_en && ren_d2 && ocntr<=i+1)
			ocntr <= ocntr + 'b1;
		if (clk_en && ren_d2 && (ocntr == i - no_ocntr2)) begin
			cmp_out2 <= out2;
			done2 <= 1'b1;
		end
	end
end


always @(posedge clk) begin
	if(rst || cntr3<j+bound3) begin
		done3 <= 1'b0;
	end else if (cntr3>=j+bound3 && ren_d3 && !done3) begin
		cmp_out3 <= out3;
		done3 <= 1'b1;
	end 
end

CONFIG: assume property (@(posedge clk) tile_en);
HANDLE_CLK_EN: assume property (@(posedge clk) $fell(rst) |-> ocntr=='b0 && done2==1'b0 && ren_d2==1'b0 && no_ocntr2=='b0 && cntr2=='b0);

SAME_ARCH_i_READ: assume property (@(posedge clk) arch_st_done1 && arch_st_done3 && in[i][33:32]==2'b1 |-> arch_st1_i==arch_st3_i);
SAME_ARCH_iplus1_READ: assume property (@(posedge clk) arch_st_done1 && arch_st_done3 &&  in[i+1][33:32]==2'b1 |-> arch_st1_i1==arch_st3_i1);

FC: assert property (@(posedge clk) done3 && done2 && arch_st_done1 |-> cmp_out3 == cmp_out2);

endmodule 
