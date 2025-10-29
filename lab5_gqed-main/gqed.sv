module gqed #(
    parameter SEQ_LEN = 32
)
(
    input [10:0] x_1,
    input [9:0] y_1,
    input [10:0] x_2,
    input [9:0] y_2,


    
    input clk, rst,

    input [$clog2(SEQ_LEN)-1:0] i, 
    input bmc_in_valid2, // BMC chooses input to be valid or invalid in the second copy. 
    // Note that BMC should be able to exercise all possible input sequences in the second copy. 
    // Otherwise, there will be completeness issues.

    input [33:0] bmc_in_invalid2

);

    wire [7:0] read_address_1;
    wire [7:0] read_sample_1;

    wire [7:0] read_address_2;
    wire [7:0] read_sample_2;

    ram ROM_1(.clk(clk), .addr(read_address_1), .dout(read_sample_1));
 
    ram ROM_2(.clk(clk), .addr(read_address_2), .dout(read_sample_2));

    assume property (@(posedge clk) ROM_1.array[in_saved_1[0][10:0]] == ROM_2.array[in_saved_2[0][10:0]] && 
                                    ROM_1.array[in_saved_1[1][10:0]] == ROM_2.array[in_saved_2[1][10:0]]);

    wire valid_1, read_index_1;
    wire valid_pixel_1;
    
    wire valid_2, read_index_2;
    wire valid_pixel_2;

    wire [7:0] wd_r_1, wd_g_1, wd_b_1;
    wire [7:0] wd_r_2, wd_g_2, wd_b_2;

    wave_display wd_1(
        .clk(clk),
        .reset(rst),
        .x(x_1),
        .y(y_1),
        .valid(valid_1),
        .read_address(read_address_1),
        .read_value(read_sample_1),
        .read_index(read_index_1),
        .valid_pixel(valid_pixel_1),
        .r(wd_r_1), .g(wd_g_1), .b(wd_b_1)
    );

    wave_display wd_2(
        .clk(clk),
        .reset(rst),
        .x(x_2),
        .y(y_2),
        .valid(valid_2),
        .read_address(read_address_2),
        .read_value(read_sample_2),
        .read_index(read_index_2),
        .valid_pixel(valid_pixel_2),
        .r(wd_r_2), .g(wd_g_2), .b(wd_b_2)
    );



reg [$clog2(SEQ_LEN)-1:0] i_cntr_1, o_cntr_1;
reg [$clog2(SEQ_LEN)-1:0] i_cntr_2, o_cntr_2;
reg [1:0] lat_cntr;

always @(posedge clk) begin
    if (rst) begin
        lat_cntr <= 0;
    end else if(lat_cntr<2) begin
        lat_cntr <= lat_cntr + 1;
    end
end


reg [15:0] in_saved_1 [0:1];
reg [15:0] in_saved_2 [0:1];
reg [23:0] out_saved_1;
reg [23:0] out_saved_2;
reg done_1, done_2;

always @(posedge clk) begin
    if(rst) begin
        i_cntr_1 <= 0;
        i_cntr_2 <= 0;
        in_saved_1 <= '{default:0};
        in_saved_2 <= '{default:0};
    end else begin
        i_cntr_1 <= i_cntr_1 + 1; 
        if(i_cntr_1 == i) 
            in_saved_1[0] <= {y_1, x_1};
        if(i_cntr_1 == i+1) 
            in_saved_1[1] <= {y_1, x_1}; 
        if(i_cntr_1 == 0)
            in_saved_2[0] <= {y_2, x_2};
        if(i_cntr_1 == 1)        
            in_saved_2[1] <= {y_2, x_2}; 
        end
    end     



always @(posedge clk) begin
    if (rst) begin
        o_cntr_1 <= 0;
        o_cntr_2 <= 0;
        out_saved_1 <= 0;
        out_saved_2 <= 0;
        done_1 <= 0;
        done_2 <= 0;
    end else 
        if (lat_cntr == 2) begin
            o_cntr_1 <= o_cntr_1 + 1;
            if(o_cntr_1 == i) begin 
                out_saved_1 <= {wd_r_1, wd_g_1, wd_b_1};
                done_1 <= 1;
            end
        end 
        if (lat_cntr == 2) begin
            o_cntr_2 <= o_cntr_2 + 1;
            if(o_cntr_2 == 0) begin 
                out_saved_2 <= {wd_r_2, wd_g_2, wd_b_2};
                done_2 <= 1;
            end
        end 
    end

assume property (@(posedge clk) $stable(i)); 

assume property (@(posedge clk) ((read_index_1 == read_index_2) && $stable(read_index_1) && $stable(read_index_2)));

FC: assert property (@(posedge clk) done_1 && done_2 && in_saved_1 == in_saved_2 |-> out_saved_1 == out_saved_2);


endmodule 



module ram (
    input clk,
    input [7:0] addr,
    output reg [7:0] dout
);
  reg [7:0] array [0:31];
    always @(posedge clk) begin
        dout <= array[addr];
    end

assume property (@(posedge clk) $stable(array));

endmodule

// TODO: GOES IN THE GQED MODULE
// SAC_valid: assume property (@(posedge clk)done_2 |-> out_save_2 == F(in_saved_2[15:8], in_saved_2[7:0], ROM_1.array[in_saved_2[15:8]], in_saved_2==0?0:ROM_2.array[in_save_2[15:0]]));
// SAC_invalid: assume property (@(posedge clk) !valid_pixel_2 |-> out_save_2 == 0);

// // -----------------------------------------------------------------------------
// // Function: F
// // Purpose : Given x, y, current read_value, and previous read_value,
// //           compute the RGB color {r,g,b} exactly as in wave_display.
// // -----------------------------------------------------------------------------
// function automatic logic [23:0] F (
//     input logic [10:0] x,          // horizontal coordinate [0..1279]
//     input logic [9:0]  y,          // vertical coordinate [0..1023]
//     input logic [7:0]  read_value,         // current sample from RAM
//     input logic [7:0]  prev_read_value     // previous sample from RAM
// );
//     // Intermediate signals
//     logic [7:0] read_value_adj, prev_read_value_adj, translated_y;
//     logic moving_up, make_white, valid_pixel;

//     // Adjust the RAM values (downshift + offset)
//     read_value_adj      = ({1'b0, read_value[7:1]}) + 8'd32;
//     prev_read_value_adj = ({1'b0, prev_read_value[7:1]}) + 8'd32;

//     // Translate y coordinate (half-resolution vertical space)
//     translated_y = y[8:1];

//     // Determine slope direction
//     moving_up = (read_value_adj < prev_read_value_adj);

//     // Determine whether this pixel lies on the waveform line
//     make_white = moving_up ?
//         ((prev_read_value_adj >= translated_y) && (read_value_adj <= translated_y)) :
//         ((prev_read_value_adj <= translated_y) && (read_value_adj >= translated_y));

//     // Valid pixel region: middle horizontal band and upper half of screen
//     valid_pixel = (
//         ((x[10:8] == 3'b001) || (x[10:8] == 3'b010)) &&
//         (x > 11'b00100000010) &&
//         (y[9] == 1'b0)
//     );

//     // Compute final RGB value
//     if (make_white && valid_pixel)
//         F = 24'hFFFFFF;  // white pixel (waveform trace)
//     else
//         F = 24'h000000;  // black pixel (background)
// endfunction