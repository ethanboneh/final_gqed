module gqed( clk, reset, data, seq_len, lit_list,  pause  );

  input clk;
  input reset;
  input [4:0] seq_len;
  input pause;
  input lit_list [31:0];
  input  [1023:0] data ;
  parameter MAX_OUT_SEQ_LEN = 300; // Arbitrary number greater than number of expected outputs and less than max value of i_raddr register to prevent overflow
  parameter BOUND = 8;
 
  reg [2:0] imode;
  reg odone;
  reg [23:0] o_iprogress;
  reg [23:0] o_oprogress;
  reg [23:0] o_oprogress_d1;
  reg [7:0]  odata;
  reg [8:0]  i_waddr;
  reg [8:0]  i_raddr;
  reg [7:0]  idata;
 reg [2:0]  pause_ctr; 
  reg [24:0] capture_data;
  reg [9:0] data_ptr;
  reg lit_type;
  reg [4:0] seq_cnt_d1;


  reg [2:0]  waddr;
  
  reg dstart; //flag indicating whether decompression has occurred
  reg qed_check;
  reg [7:0] byte_counter;
  reg [4:0] seq_cnt;

  deflate DUT ( .i_mode(imode), .o_done(odone), .i_data(idata), .o_iprogress(o_iprogress), .o_oprogress(o_oprogress), .o_byte(odata), .i_waddr(i_waddr), .i_raddr(i_raddr), .clk(clk), .reset(reset));

  always @(posedge clk) begin
	if(reset) 
		byte_counter <= 'b0;	
	else if(imode==3'b001 )
		byte_counter <= byte_counter + 'b1;		
  end 

  

  assign idata = byte_counter==0? 8'h18: (byte_counter==1? 8'h19 : data[(byte_counter-'d2)*8+:8]);


  // write always block
  always@( posedge clk ) begin
  if( reset ) begin
    i_waddr <= 0;
    waddr <= 0;
  end
  else begin
    if( imode == 3'b001 ) begin
      i_waddr <= i_waddr + 1'b1;
    end
    else if(imode == 3'b100) begin
      i_waddr <= 0;
    end
  end
  end


  //read always block
  reg [4:0] out_ctr ;
  reg [1:0] out_ctr2 ;


  always@(posedge clk) begin
    if( reset ) begin
      i_raddr <= 0;
      out_ctr <= 'b0;
      out_ctr2 <= 'b0;
      o_oprogress_d1 <= 'b0;
    end
    else begin
      o_oprogress_d1 <= o_oprogress; 
      if( i_raddr + 1 < o_oprogress && i_raddr < MAX_OUT_SEQ_LEN ) begin
        i_raddr <= i_raddr + 1'b1;
        if(o_oprogress_d1 != o_oprogress ) begin
	  if(!lit_list[out_ctr]) 
		out_ctr2 <= out_ctr2 + 1'b1;
	  if(lit_list[out_ctr] || (!lit_list[out_ctr] && out_ctr2=='d2)) begin
		out_ctr <= out_ctr + 1'b1;
		out_ctr2 <= 'b0;
	  end
        end
    end
  end
end 

reg [$clog2(32*BOUND)-1:1] resp_ctr;

always @(posedge clk) begin

	if(reset)
		resp_ctr <= 0;
	else if (byte_counter >= (data_ptr>>3)+8'd1 + (data_ptr%8!=0)) 
		resp_ctr <= resp_ctr + 1'b1;
end

  rb_property: assert property ( @( posedge clk ) resp_ctr>BOUND*seq_len  |->  out_ctr==seq_len );


  //Control FSM
  always @(posedge clk) begin
    
    if( reset ) begin
      imode <= 0; //IDLE
      pause_ctr <= 0;
    
    end
    else begin
      if( (byte_counter < ((data_ptr>>3)+8'd1 + (data_ptr%8!=0)))) begin
        imode <= 3'b001;
      end
      else if ( byte_counter == ((data_ptr>>3)+8'd1 + (data_ptr%8!=0)) ) begin
        imode <= 3'b100; //START decompression
      end
     else
	imode <= 3'b000;
  end
end


  always @(posedge clk) begin
   if ( reset || out_ctr==seq_len) begin
	seq_cnt <= 'b0; 
	data_ptr <= 'b0;
   end else if (seq_cnt<seq_len) begin
	if(lit_list[seq_cnt]) begin
		capture_data <= data[data_ptr+:'d18];
		data_ptr <= data_ptr + 'd18;
		lit_type <= lit_list[seq_cnt];
		seq_cnt_d1 <= seq_cnt;
	end else begin
		capture_data <= data[data_ptr+:'d22];
		data_ptr <= data_ptr + 'd22;
		lit_type <= lit_list[seq_cnt];
		seq_cnt_d1 <= seq_cnt;
	end
  	seq_cnt <= seq_cnt + 1'b1;
     end     
  end 

 

  // Block Header Input constraints
  c6: assume property ( @(posedge clk) capture_data[2:0] == 3'b010 ); //Not last block
  
  assume property ( @(posedge clk) lit_type |-> {capture_data[3], capture_data[4], capture_data[5], capture_data[6], capture_data[7], capture_data[8], capture_data[9], capture_data[10]} >= 8'b00110000 );
  assume property ( @(posedge clk) lit_type |-> {capture_data[3], capture_data[4], capture_data[5], capture_data[6], capture_data[7], capture_data[8], capture_data[9], capture_data[10]} <= 8'b10111111 );
  assume property ( @(posedge clk) lit_type |-> {capture_data[11], capture_data[12], capture_data[13], capture_data[14], capture_data[15], capture_data[16], capture_data[17]}  == 7'b0 );


  assume property ( @(posedge clk) !lit_type |-> {capture_data[3], capture_data[4], capture_data[5], capture_data[6], capture_data[7], capture_data[8], capture_data[9]} == 7'b0000001 );//length hardcoded to 3. 3 repititions possible.
  assume property ( @(posedge clk) !lit_type |-> {capture_data[15], capture_data[16], capture_data[17], capture_data[18], capture_data[19], capture_data[20], capture_data[21]}  == 7'b0 );

//distance can choose from 1,2,3,4 depending on the position of the alphabet
  assume property ( @(posedge clk) !lit_type && seq_cnt_d1=='d1 |-> {capture_data[10], capture_data[11], capture_data[12], capture_data[13], capture_data[14]} == 5'd0 );
  assume property ( @(posedge clk) !lit_type && seq_cnt_d1=='d2 |-> (({capture_data[10], capture_data[11], capture_data[12], capture_data[13], capture_data[14]} == 5'd0) ||  ({capture_data[10], capture_data[11], capture_data[12], capture_data[13], capture_data[14]} == 5'd1)));
  assume property ( @(posedge clk) !lit_type && seq_cnt_d1=='d3 |-> (({capture_data[10], capture_data[11], capture_data[12], capture_data[13], capture_data[14]} == 5'd0) ||  ({capture_data[10], capture_data[11], capture_data[12], capture_data[13], capture_data[14]} == 5'd1) ||  ({capture_data[10], capture_data[11], capture_data[12], capture_data[13], capture_data[14]} == 5'd2)));
  assume property ( @(posedge clk) !lit_type && seq_cnt_d1>'d3 |-> (({capture_data[10], capture_data[11], capture_data[12], capture_data[13], capture_data[14]} == 5'd0) ||  ({capture_data[10], capture_data[11], capture_data[12], capture_data[13], capture_data[14]} == 5'd1) ||  ({capture_data[10], capture_data[11], capture_data[12], capture_data[13], capture_data[14]} == 5'd2) ||  ({capture_data[10], capture_data[11], capture_data[12], capture_data[13], capture_data[14]} == 5'd3)));

assume property (@(posedge clk) (byte_counter == (data_ptr>>3)+8'd1 + (data_ptr%8!=0)) |->  data[((byte_counter-'d2)*8+data_ptr%8)+:8]==8'h18);
assume property (@(posedge clk) $stable(data) && $stable(lit_list) && $stable(seq_len) && seq_len>0 && lit_list[0]!=0);

endmodule

