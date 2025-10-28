
// ------------------------------------------------------------------
//   Design Unit:    GQED_rtl
// ------------------------------------------------------------------


// We will check FC of read action
// auv = action under verification
// Though there exists a solution such that the code apart from /*Fill*/ and /*Code goes here*/ needs no modification, feel free to modify the code as per convenience.

module gqed
#(
parameter SEQ_LEN = 32, // Maximum length of the Pre-sequence. 
RESP_BOUND = 2 // Upper bound estimate of the number of clock cycles for read action to finish execution 
)
(
input clk, rst,
// BMC controlled inputs
input clk_en, // BMC chooses when to enable clock for second copy 

input [32:0] bmc_in [0:SEQ_LEN-1], // The sequence of inputs (action, data) chosen by the BMC solver. 
// First 16 bits (bmc_in[*][15:0]) is address, next 16 bits (bmc_in[*][31:16]) is data 
// The MSB (bmc_in[*][32]) decides action (read (bmc_in[*][32]==1'b0), write (bmc_in[*][32]==1'b1)).

input [$clog2(SEQ_LEN)-1:0] i, // index of action under verification in the sequence of inputs (bmc_in). 

input bmc_in_valid2, // BMC chooses input to be valid or invalid in the second copy. 
// Note that BMC should be able to exercise all possible input sequences in the second copy. 
// Otherwise, there will be completeness issues.

input [33:0] bmc_in_invalid2 //Used as invalid/dont-care input to the second copy. 
// Note that bmc_in_invalid2[33:32] feeds ren_in and wen_in separately. 
);
// Note that bmc_in[0 .. i-1] is considered pre-sequence, executed on first and second copy
// bmc_in[i] is action under verification, executed on second and third copy 
// after action under verification, second copy executes post sequence which is dont care for the property (bmc_in_invalid2 is used)

  // 3 copy instantiation
  wire [15:0] addr_in1, data_in1, out1, addr_in2, data_in2, out2, addr_in3, data_in3, out3; 
  wire wen_in1, ren_in1, wen_in2, ren_in2, wen_in3, ren_in3; 

  memory_core copy1 (
    .clk(clk),
    .clk_en(1'b1), // copy1 is always clock enabled
    .reset(rst),
    .flush(1'b0), // Not used in this experiment
    .config_en_sram(4'b0), // Not used in this experiment
    .enable_chain(1'b0), // Not used in this experiment
    .tile_en(1'b1), // Not used in this experiment
    .addr_in(addr_in1),
    .data_in(data_in1),
    .wen_in(wen_in1),
    .ren_in(ren_in1),
    .mode(2'd2),
    .data_out(out1) ); // Not used in this experiment

  memory_core copy2 (
    .clk(clk),
    .clk_en(clk_en), // BMC solver chooses when to clock enable copy2
    .reset(rst),
    .flush(1'b0), // Not used in this experiment
    .config_en_sram(4'b0), // Not used in this experiment
    .enable_chain(1'b0), // Not used in this experiment
    .tile_en(1'b1), // Not used in this experiment
    .addr_in(addr_in2), 
    .data_in(data_in2),
    .wen_in(wen_in2),
    .ren_in(ren_in2),
    .mode(2'd2), // Not used in this experiment
    .data_out(out2));

  memory_core copy3 (
    .clk(clk),
    .clk_en(1'b1), // copy3 is always clock enabled
    .reset(rst),
    .flush(1'b0), // Not used in this experiment
    .config_en_sram(4'b0), // Not used in this experiment
    .enable_chain(1'b0), // Not used in this experiment
    .tile_en(1'b1), // Not used in this experiment
    .addr_in(addr_in3), 
    .data_in(data_in3),
    .wen_in(wen_in3),
    .ren_in(ren_in3),
    .mode(2'd2), // Not used in this experiment
    .data_out(out3));


/*
  Logic for input index tracking counter. 
  input at index i is considered action under verificaiton.
  bmc_in[0 ... i-1] is fed to first copy and after that it idles (ren = 0 and wen = 0). 
  bmc_in[0 ... i] is fed to second copy and after that dont care inputs from bmc_in_invalid is fed. 
  In the third copy only bmc_in[i] is fed and after that it idles (ren = 0 and wen = 0). 
  We need input index tracking counters to track valid input fed to each copy. 
  Note that clock is always enabled in the first and third copies. 
  Keep in mind that only count valid inputs for copy2 (i.e. when bmc_in_valid2 and clk_en are both high).
  Make sure to prevent the counters from overflowing.
 
  Signals to use: cntr1, cntr2, cntr3, i, bmc_in_valid2, clk_en    
  */

  logic [$clog2(SEQ_LEN):0] cntr1, cntr2, cntr3; // keeps track of sequence index of the inputs being fed to the three copies.
  always @(posedge clk) begin
    if (rst) begin
      cntr1 <= 0;
      cntr2 <= 0;
      cntr3 <= 0;
    end else begin
      if (cntr1 < i) begin // copy 1 should execute up to and not including auv
        cntr1 <= cntr1 + 'b1;
      end
      if (clk_en && bmc_in_valid2 && cntr2 <= i) begin // copy2 should excute tp to and including auv 
        cntr2 <= cntr2 + 'b1;
      end
      if (cntr3 < 1) begin // copy 3 should execute only auv 
        cntr3 <= cntr3 + 'b1;
      end
    end
  end

  // ------------------------------------------------------------------   


  /*
     assign values to input signals of each copy using the input index counters and bmc_in
     keep in mind that: 
      First 16 bits (bmc_in[*][15:0]) is address, next 16 bits (bmc_in[*][31:16]) is data 
      The MSB (bmc_in[*][32]) decides action (read (bmc_in[*][32]==1'b0), write (bmc_in[*][32]==1'b1)).
     Signals to use: i, bmc_in, cntr1, bmc_in_valid2, cntr2, cntr3
  */ 

  // copy 1

  assign addr_in1 = bmc_in[cntr1][15:0]; // read data from bmc_in based of counter position. 
  assign data_in1 = bmc_in[cntr1][31:16]; // similarly read address 

  /*
     To write, wen_in has to be high. We don't care about ren_in (1'bx). To read, wen_in == 1'b0 and ren_in == 1'b1. 
     For first copy, after i-1 inputs, we have to idle i.e. no valid inputs (wen_in == 1'b0 and ren_in == 1'b0). 
     Hint: can use nested ternary operators 
  */

  assign wen_in1 =  cntr1<i ?  bmc_in[cntr1][32] : 1'b0; 
  assign ren_in1 =  cntr1<i ? (bmc_in[cntr1][32] ? 1'bx : 1'b1) : 1'b0;
// ------------------------------------------------------------------   

// copy 2

  /*
    Fill in similar to first copy. Now we have to send the inputs up to i from bmc_in. 
    If BMC decides to send an invalid input (bmc_in_valid2 == 1'b0) and for inputs after auv, feed from bmc_in_invalid2. 
  */

  assign addr_in2 = bmc_in_valid2 && cntr2 <= i ?  bmc_in[cntr2][15:0] : bmc_in_invalid2[15:0];
  assign data_in2 = bmc_in_valid2 && cntr2 <= i ?  bmc_in[cntr2][31:16]: bmc_in_invalid2[31:16];
  assign wen_in2  = bmc_in_valid2 && cntr2 <= i ?  bmc_in[cntr2][32]   : (cntr2 <= i ? 1'b0 : bmc_in_invalid2[33]);
  assign ren_in2  = bmc_in_valid2 && cntr2 <= i ? (bmc_in[cntr2][32]?1'bx:1'b1) : (cntr2 <= i ? 1'b0 : bmc_in_invalid2[32]);
// ------------------------------------------------------------------   

// copy 3

  /*
     Fill in similar to first copy. We only care about auv. 
  */

  assign addr_in3 = cntr3 == 'b0 ?  bmc_in[i][15:0]  : 0;
  assign data_in3 = cntr3 == 'b0 ?  bmc_in[i][31:16] : 0;
  assign wen_in3  = cntr3 == 'b0 ?  bmc_in[i][32]    : 1'b0;
  assign ren_in3  = cntr3 == 'b0 ? (bmc_in[i][32] ? 1'bx :1'b1) : 1'b0;

// ------------------------------------------------------------------   

  // arch state assumption
  logic [$clog2(RESP_BOUND):0] idle_cntr1; // Counts for RESP_BOUND clock cycles after i-1 inputs have been fed to first copy. 
  logic [15:0] final_arch_st1; // saves final value of the arch state (mem_inst_0) after idling in the first copy.
  logic [15:0] init_arch_st3;  // saves value of the arch state (mem_inst_0) right after reset in the third copy.
  logic arch_st1_done;         // goes high when the arch state is saved in first copy.

/*
  We need to save arch state of first copy after the waiting for RESP_BOUND clock cycles after inputs up to i-1 are sent in the first copy
  For the third copy, we save the initial value of the arch state. 
  Note that the bit 9 of the address is used to select between mem_inst0 (addr_in[9] == 0) and mem_inst1 (addr_in[9] == 1) and remaining 8 bits to map to access elements in the mem_inst0.sram_stub.data_array (size 512 elements each element 16 bits long).  
  addr_in[15:10] are dont cares.
  Note that you only need to save the memory element that is being read by auv (action bmc_in[i]). 
*/
  always @(posedge clk) begin
    if (rst) begin
      idle_cntr1     <= 0;
      final_arch_st1 <= 0;
      init_arch_st3  <= 0;
      arch_st1_done  <= 0;
    end else begin
      if (cntr1 == i && idle_cntr1 < RESP_BOUND) begin
        idle_cntr1 <= idle_cntr1 + 'b1;
      end
      if (idle_cntr1 == RESP_BOUND) begin
        if(bmc_in[i][9])
				  final_arch_st1 <= copy1.mem_inst1.sram_stub.data_array[bmc_in[i][8:0]];
  			else
          final_arch_st1 <= copy1.mem_inst0.sram_stub.data_array[bmc_in[i][8:0]];
        arch_st1_done <= 'b1;
      end
      if (cntr3 == 0) begin
        if(bmc_in[i][9])
				  init_arch_st3 <= copy3.mem_inst1.sram_stub.data_array[bmc_in[i][8:0]];
  			else
          init_arch_st3 <= copy3.mem_inst0.sram_stub.data_array[bmc_in[i][8:0]];
      end
    end
  end

  /*
     If arch states of first and third copies have been saved, constrain them to be equal. 
     Important signals to use: arch_st_done1, init_arch_st3 final_arch_st1   
  */

  SAME_ARCH: assume property (@(posedge clk) (arch_st1_done implies (final_arch_st1 == init_arch_st3)) );

  //FC check:
  /*
     Create logic for out_valid2 and out_valid3, which go high when data_out2/3 are valid. 
     data_out is valid one clock cycle after read action is sent.
     Note that clk_en is always high in third copy. 
     Remember that if wen_in is high, irrepsective of ren_in, the action will always be write so be sure to exclude that condition while updating out_valid. Out_valid* keeps track if the input in the last clock cycle was a valid read action or not. 
     Signals to use: clk_en, ren_in2, wen_in2, ren_in3, wen_in3
  */
  logic out_valid2, out_valid3; //Signals to track when out is valid. Out is generated 1 clock cycle after the read action (ren_in=1)
  always @(posedge clk) begin
    if (rst) begin
      out_valid2  <= 'b0;
      out_valid3  <= 'b0;
    end else begin
      out_valid2 <= clk_en && ren_in2 && !wen_in2; // out valid if read request sent last cycle
      out_valid3 <= ren_in3 && !wen_in3;
    end
  end

  /*
     Create logic for incrementing out_cntr2, which counts the valid outputs of second copy, no_out_cntr, which counts the write actions (no output actions) upto auv. We use these to save the output of auv in second copy. 
     The valid output for a read action action is produced 1 clock cycle later. out_valid2 captures this. Write action does not produce any output but all inputs upto i can be either write (captured in no_oout_cntr2) or read (i-no_ocntr2) actions so be sure to take that into account.  
     Important signals to use: clk_en, bmc_in_valid2, cntr2, i, bmc_in, out_valid2      
  */
  logic [$clog2(SEQ_LEN):0] out_cntr2; // keeps track of the sequence index of the outputs generated by the second copy. Output is only generated by read actions.
  logic [$clog2(SEQ_LEN):0] no_out_cntr2; // keeps track of the number of inputs that produce no output i.e. inputs with write action (bmc_in[*][32]==1'b1). 
  always @(posedge clk) begin
    if (rst) begin
      out_cntr2  <= 'b0;
      no_out_cntr2 <= 'b0;
    end else begin
      if (clk_en && bmc_in_valid2 && cntr2 <= i) begin
        if (bmc_in[cntr2][32]) begin
          no_out_cntr2 <= no_out_cntr2 + 'b1;
        end
      end
      if (out_cntr2 <= i && out_valid2) begin
        out_cntr2 <= out_cntr2 + 'b1;
      end
    end
  end

  /*
    create a logic for saving the output of auv from second and third copy to auv_out2/3. set done2/3 signal when the ourput is saved.
     Important signals to use: out_cntr2, no_out_cntr2, i, out_valid2, out_valid3      
  */

  logic done2, done3;

  logic [15:0] auv_out2; // auv_out2 saves output of auv from the second copy.
  logic [15:0] auv_out3; // auv_out3 saves output of auv from the third copy. The first output produced by the third copy belongs to auv, since third copy only executes auv.

  always @(posedge clk) begin
    if (rst) begin
      done2       <= 'b0;
      done3       <= 'b0;
    end else begin
      if ( ( (out_cntr2 + no_out_cntr2) == i ) && out_valid2 && !done2) begin
        done2     <= 'b1;
        auv_out2  <= out2;
      end
      if (out_valid3) begin
        done3    <= 'b1;
        auv_out3 <= out3;
      end
    end
  end

  /*
     when outputs from second and third copy and arch state from the first copy are saved, check if the output of the auv from second and third copy are the same. 
     Important signals to use: done3, done2, arch_st_done1, auv_out3, auv_out2     
  */

  FC: assert property( @(posedge clk) ( (arch_st1_done && done2 && done3) implies (auv_out2 == auv_out3) ) );

  // Assumptions:

  AUV_READ: assume property (@(posedge clk) bmc_in[i][32] == 1'b0); // we will check FC of read action only. 

  /*
     Write constraints for input signals and the arch state. in and i needs to be held constant. The arch state right after reset should be the same for the first and second copies otherwise even the same input preseqeuence will not guarantee same arch state.
     Signals to use: i, bmc_in, rst,  copy1.mem_inst0.sram_stub.data_array, copy1.mem_inst1.sram_stub.data_array, copy2.mem_inst0.sram_stub.data_array, copy2.mem_inst1.sram_stub.data_array
  */  

  STABLE: assume property ( @(posedge clk) ( $stable(bmc_in) && $stable(i)) );
  SAME_ARCH_AT_RST: assume property (@(posedge clk) $fell(rst) |-> 
    copy1.mem_inst0.sram_stub.data_array == copy2.mem_inst0.sram_stub.data_array && 
      copy1.mem_inst1.sram_stub.data_array == copy2.mem_inst1.sram_stub.data_array); 

endmodule 
