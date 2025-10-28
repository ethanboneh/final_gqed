module gqed
#(
parameter SEQ_LEN = 16
)
(
input clk, rst,
input [15:0] in [0:SEQ_LEN-1],
input [$clog2(SEQ_LEN)-1:0] i,
input in_vld,
input host_rdy,
input [15:0] bmc_in
);

STABLE: assume property (@(posedge clk) $stable(in) && $stable(i));

reg [$clog2(SEQ_LEN)-1:0] cntr, ocntr;

wire out_vld1, out_vld2;

wire clk_en;

wire [15:0] out1, out2;

reg host_rdy_d;


memory_core copy1(.clk(clk),  .clk_en(clk_en), .reset(rst), .data_in(cntr<=i & in_vld?in[cntr]:bmc_in), .data_out(out1), .wen_in(in_vld), .ren_in(host_rdy), .valid_out(out_vld1));


  reg [$clog2(SEQ_LEN)-1:0] count_ren;
  reg [$clog2(SEQ_LEN)-1:0] count_wen; 

   CONFIG_CPY1 : assume property ( @(posedge clk) (copy1.flush==1'b0) && (copy1.config_en_sram==4'b0) && (copy1.config_addr==32'h0) && (copy1.enable_chain==1'b0) &&  (copy1.circular_en == 1'b1) && (copy1.almost_count == 4'h0) && (copy1.mode == 2'h1) && (copy1.tile_en == 1'b1) && $stable(copy1.depth) && (count_ren+copy1.depth>=count_wen));

  always @(posedge clk) begin
	if(rst) begin
		count_ren <= 0;
		count_wen <= 0;
	end
	else begin
		if(clk_en && host_rdy && out_vld1)		
			count_ren <= count_ren + 1;
		if(clk_en && in_vld)
			count_wen <= count_wen + 1;
	end
end



memory_core copy2(.clk(clk),  .clk_en(1'b1), .reset(rst), .data_in(in[i]), .data_out(out2), .wen_in(1'b1), .ren_in(1'b1), .valid_out(out_vld2));


   CONFIG_CPY2 : assume property ( @(posedge clk) (copy2.flush==1'b0) && (copy2.config_en_sram==4'b0) && (copy2.config_addr==32'h0) && (copy2.enable_chain==1'b0) &&  (copy2.circular_en == 1'b1) && (copy2.almost_count == 4'h0) && (copy2.mode == 2'h1) && (copy2.tile_en == 1'b1) && $stable(copy2.depth) && copy2.depth>0);
			
always @(posedge clk) begin
  if(rst) begin
    host_rdy_d <= 1'b0;
  end else if (clk_en) begin
    host_rdy_d <= host_rdy;
  end
end

always @(posedge clk) begin
	if(rst) begin
		cntr <= 'b0;
		ocntr <= 'b0;
	end else begin 
		if (clk_en && in_vld && cntr<=i+1)
			cntr <= cntr + 'b1;
		if (clk_en && host_rdy_d && out_vld1 && ocntr<=i+1) 
			ocntr <= ocntr + 'b1;
	end
end



reg [15:0] cmp_out1;
reg [15:0] cmp_out2;
reg done1, done2;

always @(posedge clk) begin
	if(rst) begin
		done1 <= 1'b0;
    done2 <= 1'b0;
	end else begin	
		if (out_vld2 && !done2) begin 
			cmp_out2 <= out2;
      done2 <= 1;
		end if (clk_en && host_rdy_d && out_vld1 && ocntr == i && !done1) begin
			cmp_out1 <= out1;
			done1 <= 1;
		end
	end
end


FC: assert property (@(posedge clk) done1 && done2 |-> cmp_out1 == cmp_out2);


endmodule 
