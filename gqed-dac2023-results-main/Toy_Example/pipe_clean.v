module Pipe(
input clk, rst,
input [1:0] data,
input action,
output [1:0] out, 
input in_vld,
output out_vld
);

reg [2:0] pipe [3:0]; //pipe[2][1:0] is arch state
reg [3:0] pipev;

always @(posedge clk) begin
	if(rst)
		pipev <= 4'b0;
	else begin
		pipev[0] <= in_vld;
		pipev[1] <= pipev[0];
		pipev[2] <= pipev[1];
		pipev[3] <= pipev[2];			
	end
	if (in_vld)
		pipe[0] <= {action, data};
	if (pipev[0])		
		pipe[1] <= pipe[0];
	if (pipev[1])		
		pipe[2][1:0] <= pipe[1][1:0]^(pipe[1][2]?2'b01:pipe[2][1:0]);
	if (pipev[2])
		pipe[3] <= pipe[2];
end  

assign out = pipe[3][1:0];
assign out_vld = pipev[3];

endmodule 




