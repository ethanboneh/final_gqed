module gqed
#(
parameter SEQ_LEN = 16
)
(
input clk, rst,
input [7:0] in [0:SEQ_LEN-1],
input [$clog2(SEQ_LEN)-1:0] i,
input in_vld,
input [7:0] bmc_in
);

STABLE: assume property (@(posedge clk) $stable(in) && $stable(i) && !i[0]);

reg [$clog2(SEQ_LEN)-1:0] cntr1, cntr2, ocntr1, ocntr2;

wire en1, en2, wr1, wr2;

wire [7:0] out1, out2;

wire [3:0] addr1;
wire ap_start2;

reg wr1_d, wr2_d, en1_d, en2_d;
reg [3:0] addr1_d;
			
workload copy1 (.ap_clk(clk), .ap_rst(rst), .data_address0(addr1), .data_ce0(en1), .data_we0(wr1), .data_d0(out1), .data_q0((wr1_d||!en1_d)?bmc_in:in[addr1_d]), .data_offset({ocntr1>>2,2'b0}));
workload copy2 (.ap_clk(clk), .ap_rst(rst), .ap_start(ap_start2), .data_ce0(en2), .data_we0(wr2), .data_d0(out2), .data_q0(in[i+cntr2]), .data_offset(4'b0));


always @(posedge clk) begin
  wr1_d <= wr1;
  wr2_d <= wr2;
  en1_d <= en1;
  en2_d <= en2;
  addr1_d <= addr1;
end

always @(posedge clk) begin
	if(rst) begin
		cntr1 <= 'b0;
		cntr2 <= 'b0;
	end else begin 
		if (en1_d && !wr1_d && cntr1<=i+2)
			cntr1 <= cntr1 + 'b1;
		if (cntr2<2 && !wr2_d && en2_d) 
			cntr2 <= cntr2 + 'b1;
	end
end


CPY2_STABLE_ST: assume property (@(posedge clk) cntr2==1  |-> !ap_start2);   

reg [7:0] cmp_out1 [0:1];
reg [7:0] cmp_out2 [0:1];
reg done1, done2;

always @(posedge clk) begin
	if(rst) begin
		done1 <= 1'b0;
		done2 <= 1'b0;
		ocntr1 <= 'b0;
		ocntr2 <= 'b0;		
	end else begin 
		if (en1_d && wr1_d && ocntr1<=i+2)
			ocntr1 <= ocntr1 + 'b1;
		if (en2_d && wr2_d && ocntr2<=2)
			ocntr2 <= ocntr2 + 'b1;			
		if (en2_d && wr2_d && ocntr2 == 0 && !done2) 
			cmp_out2[0] <= out2;
		if (en2_d && wr2_d && ocntr2 == 1 && !done2) begin
			cmp_out2[1] <= out2;
			done2 <= 1;
		end if (en1_d && wr1_d && ocntr1 == i && !done1)
			cmp_out1[0] <= out1;
		if (en1_d && wr1_d && ocntr1 == i+1 && !done1) begin
			cmp_out1[1] <= out1;
			done1 <= 1;
		end
	end
end


FC: assert property (@(posedge clk) done1 && done2 |-> cmp_out1 == cmp_out2);

generate
  for (genvar i=0; i < 32; i++) begin
  CONSISTENT_KEY : assume property
    (@(posedge clk) (
                     $stable(copy1.local_key_0_U.workload_local_key_0_rom_U.ram[i]) && $stable(copy2.local_key_0_U.workload_local_key_0_rom_U.ram[i]) && (copy1.local_key_0_U.workload_local_key_0_rom_U.ram[i] == copy2.local_key_0_U.workload_local_key_0_rom_U.ram[i]) ));
   end
endgenerate


endmodule 
