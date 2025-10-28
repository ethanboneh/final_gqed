module mac #(
  parameter WIDTH = 4
)(
  input logic clk, 
  input logic rst, 
  input logic in_valid, 
  input logic in_action, 
  input logic [WIDTH-1:0] in_data_a, 
  input logic [WIDTH-1:0] in_data_b, 
  output logic out_valid, 
  output logic [(WIDTH*2)-1:0] out_data
);
  parameter SETVAL = 0;
  parameter MAC    = 1;
  logic [(WIDTH*2)-1:0] ACC;
  logic [(WIDTH*2)-1:0] s1_data;
  logic s1_valid;
  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
      s1_data   <= 0;
      s1_valid  <= 0;
      ACC       <= 0;
      out_valid <= 0;
      out_data  <= 0;
    end else begin
      // Stage 1
      if (in_action == SETVAL) begin
        s1_data <= {in_data_a, in_data_b};
      end else if (in_action == MAC) begin
        s1_data <= (in_data_a * in_data_b) + ACC;
      end
      s1_valid <= in_valid;

      // Stage 2
      out_valid <= s1_valid;
      if (s1_valid) begin
        ACC <= s1_data;
        out_data <= s1_data;
      end
    end
  end
endmodule

