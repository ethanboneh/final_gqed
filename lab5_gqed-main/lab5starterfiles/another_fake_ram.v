module another_fake_ram (
    input clk,
    input [7:0] addr,
    output [7:0] dout
);
  reg [7:0] ram [0:127];
    always @(posedge clk)
        dout = ram[addr];
assume property (@posedge clk $stable(ram));
endmodule