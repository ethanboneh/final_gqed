module wave_display (
    input clk,
    input reset,
    input [10:0] x,  // [0..1279]
    input [9:0]  y,  // [0..1023]
    input valid,
    input [7:0] read_value,
    input read_index,
    output wire [8:0] read_address,
    output wire valid_pixel,
    output wire [7:0] r,
    output wire [7:0] g,
    output wire [7:0] b
);

    // declarations
    reg [8:0] read_address_reg;
    reg care;
    
    
    wire [7:0] read_value_adjusted;
    wire [8:0] previous_addr;
    wire changed_addr;
    wire [7:0] previous_value;
    wire almost_valid_pixel;
    
    // assign read value adjusted
    assign read_value_adjusted = (read_value >> 1) + 8'd32;
    
    
    // assign the read address, dropping LSB. 
    always @(*) begin
        care = 1'b0;
        read_address_reg = 1'b0;
        case(x[10:8])
            3'b001: begin
                read_address_reg = {read_index, 1'b0, x[7:1]};
                care = 1'b1;
            end
            3'b010: begin 
                read_address_reg = {read_index, 1'b1, x[7:1]};
                care = 1'b1;
            end
            default: begin
                care = 1'b0;
                read_address_reg = 1'b0;
            end
         endcase
     end
     
     
     assign read_address = read_address_reg;
     
     // check whether the address has changed
     assign changed_addr = read_address != previous_addr;
     
     // cache previous address/value for later comparisons
     dffre #(.WIDTH(9)) moving_address(.clk(clk), .r(reset), .d(read_address), .q(previous_addr), .en(changed_addr && valid));
     dffre #(.WIDTH(8)) moving_value(.clk(clk), .r(reset), .d(read_value_adjusted), .q(previous_value), .en(changed_addr && valid));
     
     
     
     // validity checking: valid and in top half and in second/third quadrants
     assign almost_valid_pixel = (y[9] == 0 && valid && care); 
     dffr #(.WIDTH(1)) validity(.clk(clk), .r(reset), .d(almost_valid_pixel), .q(valid_pixel));
    
     // go high if y is between previous and next, otherwise go low
     assign {r,g,b} = (((read_value_adjusted >= y[8:1] && previous_value <= y[8:1]) || (read_value_adjusted <= y[8:1] && previous_value >= y[8:1])) && valid_pixel) ?
                        24'hFFFFFF : 0;
    
endmodule
