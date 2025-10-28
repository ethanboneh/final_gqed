// G-QED harness for wave_display + another_fake_ram.
// Drives three copies of the DUT with Jasper-generated stimuli and
// checks functional and idle correctness while enforcing raster-scan behavior.

module gqed
#(
    parameter int SEQ_LEN      = 32, // Maximum length of the pre sequence
    parameter int RESP_BOUND   = 2,  // Cycles needed for architectural state to settle
    parameter int ACTION_WIDTH = 23  // Encoded stimulus width: {valid, x, y, read_index}
)
(
    input  logic clk,
    input  logic rst,
    input  logic clk_en,
    input  logic [ACTION_WIDTH-1:0] bmc_in [0:SEQ_LEN-1],
    input  logic [$clog2(SEQ_LEN)-1:0] i,
    input  logic bmc_in_valid2,
    input  logic [ACTION_WIDTH-1:0] bmc_in_invalid2
);

    // ------------------------------------------------------------------------
    // Stimulus encoding
    // ------------------------------------------------------------------------
    typedef struct packed {
        logic        pix_valid;
        logic [10:0] x;
        logic [9:0]  y;
        logic        read_index;
    } action_t;

    localparam action_t IDLE_ACTION = '{default:1'b0};

    action_t auv_action;
    assign auv_action = action_t'(bmc_in[i]);

    // Keep the symbolic stimuli stable so counters can safely index them.
    ASSUME_STIM_STABLE: assume property (@(posedge clk) disable iff (rst)
                                         $stable(bmc_in) && $stable(bmc_in_invalid2) && $stable(i));
    ASSUME_INDEX_RANGE: assume property (@(posedge clk) disable iff (rst)
                                         i < SEQ_LEN);

    // ------------------------------------------------------------------------
    // Input counters (first copy runs pre-sequence, third runs AUV only)
    // ------------------------------------------------------------------------
    logic [$clog2(SEQ_LEN):0] cntr1, cntr2;
    logic [1:0]               cntr3;

    always_ff @(posedge clk) begin
        if (rst) begin
            cntr1 <= '0;
            cntr2 <= '0;
            cntr3 <= '0;
        end else begin
            if (cntr1 < i) begin
                cntr1 <= cntr1 + 1'b1;
            end
            if (clk_en && bmc_in_valid2 && cntr2 <= i) begin
                cntr2 <= cntr2 + 1'b1;
            end
            if (cntr3 < 1) begin
                cntr3 <= cntr3 + 1'b1;
            end
        end
    end

    logic apply_bmc2;
    assign apply_bmc2 = clk_en && bmc_in_valid2 && (cntr2 <= i);

    // ------------------------------------------------------------------------
    // Decode actions for each copy
    // ------------------------------------------------------------------------
    action_t action1;
    assign action1 = (cntr1 < i) ? action_t'(bmc_in[cntr1]) : IDLE_ACTION;

    action_t action2_reg;
    always_ff @(posedge clk) begin
        if (rst) begin
            action2_reg <= IDLE_ACTION;
        end else begin
            if (apply_bmc2) begin
                action2_reg <= action_t'(bmc_in[cntr2]);
            end else if (cntr2 > i) begin
                action2_reg <= action_t'(bmc_in_invalid2);
            end
        end
    end

    action_t action3;
    assign action3 = (cntr3 == 0) ? auv_action : IDLE_ACTION;

    // ------------------------------------------------------------------------
    // Copy 1 wiring (pre sequence only)
    // ------------------------------------------------------------------------
    logic [10:0] x1;
    logic [9:0]  y1;
    logic        pix_valid1;
    logic        read_index1;

    assign x1         = action1.x;
    assign y1         = action1.y;
    assign pix_valid1 = action1.pix_valid;
    assign read_index1 = action1.read_index;

    logic [8:0] read_addr1;
    logic [7:0] read_addr1_ram;
    logic [7:0] ram_read_data1;
    logic       valid_pixel1;
    logic [7:0] r1, g1, b1;

    assign read_addr1_ram = read_addr1[7:0];

    another_fake_ram ram_cpy1 (
        .clk  (clk),
        .addr (read_addr1_ram),
        .dout (ram_read_data1)
    );

    wave_display wd_cpy1 (
        .clk         (clk),
        .reset       (rst),
        .x           (x1),
        .y           (y1),
        .valid       (pix_valid1),
        .read_address(read_addr1),
        .read_value  (ram_read_data1),
        .read_index  (read_index1),
        .valid_pixel (valid_pixel1),
        .r           (r1),
        .g           (g1),
        .b           (b1)
    );

    // ------------------------------------------------------------------------
    // Copy 2 wiring (pre + AUV + unconstrained tail)
    // ------------------------------------------------------------------------
    logic [10:0] x2;
    logic [9:0]  y2;
    logic        pix_valid2_in;
    logic        read_index2;

    assign x2            = action2_reg.x;
    assign y2            = action2_reg.y;
    assign pix_valid2_in = action2_reg.pix_valid;
    assign read_index2   = action2_reg.read_index;

    logic [8:0] read_addr2;
    logic [7:0] read_addr2_ram;
    logic [7:0] ram_read_data2;
    logic       valid_pixel2;
    logic [7:0] r2, g2, b2;

    assign read_addr2_ram = read_addr2[7:0];

    another_fake_ram ram_cpy2 (
        .clk  (clk),
        .addr (read_addr2_ram),
        .dout (ram_read_data2)
    );

    wave_display wd_cpy2 (
        .clk         (clk),
        .reset       (rst),
        .x           (x2),
        .y           (y2),
        .valid       (pix_valid2_in),
        .read_address(read_addr2),
        .read_value  (ram_read_data2),
        .read_index  (read_index2),
        .valid_pixel (valid_pixel2),
        .r           (r2),
        .g           (g2),
        .b           (b2)
    );

    // ------------------------------------------------------------------------
    // Copy 3 wiring (AUV only)
    // ------------------------------------------------------------------------
    logic [10:0] x3;
    logic [9:0]  y3;
    logic        pix_valid3;
    logic        read_index3;

    assign x3          = action3.x;
    assign y3          = action3.y;
    assign pix_valid3  = action3.pix_valid;
    assign read_index3 = action3.read_index;

    logic [8:0] read_addr3;
    logic [7:0] read_addr3_ram;
    logic [7:0] ram_read_data3;
    logic       valid_pixel3;
    logic [7:0] r3, g3, b3;

    assign read_addr3_ram = read_addr3[7:0];

    another_fake_ram ram_cpy3 (
        .clk  (clk),
        .addr (read_addr3_ram),
        .dout (ram_read_data3)
    );

    wave_display wd_cpy3 (
        .clk         (clk),
        .reset       (rst),
        .x           (x3),
        .y           (y3),
        .valid       (pix_valid3),
        .read_address(read_addr3),
        .read_value  (ram_read_data3),
        .read_index  (read_index3),
        .valid_pixel (valid_pixel3),
        .r           (r3),
        .g           (g3),
        .b           (b3)
    );

    // ------------------------------------------------------------------------
    // Architectural state capture (prev sample tracking registers)
    // ------------------------------------------------------------------------
    wire [8:0] prev_addr_cpy1 = wd_cpy1.change_flip_flop.q;
    wire [7:0] prev_val_cpy1  = wd_cpy1.RAM_value_flip_flop.q;

    wire [8:0] prev_addr_cpy3 = wd_cpy3.change_flip_flop.q;
    wire [7:0] prev_val_cpy3  = wd_cpy3.RAM_value_flip_flop.q;

    logic [$clog2(RESP_BOUND):0] idle_cntr1;
    logic                        arch_state_captured1;
    logic                        arch_state_captured3;
    logic [8:0]                  final_prev_addr1;
    logic [7:0]                  final_prev_val1;
    logic [8:0]                  init_prev_addr3;
    logic [7:0]                  init_prev_val3;

    always_ff @(posedge clk) begin
        if (rst) begin
            idle_cntr1           <= '0;
            arch_state_captured1 <= 1'b0;
            final_prev_addr1     <= '0;
            final_prev_val1      <= '0;
        end else begin
            if ((cntr1 == i) && (idle_cntr1 < RESP_BOUND)) begin
                idle_cntr1 <= idle_cntr1 + 1'b1;
            end
            if (!arch_state_captured1 && (idle_cntr1 == RESP_BOUND)) begin
                final_prev_addr1     <= prev_addr_cpy1;
                final_prev_val1      <= prev_val_cpy1;
                arch_state_captured1 <= 1'b1;
            end
        end
    end

    always_ff @(posedge clk) begin
        if (rst) begin
            arch_state_captured3 <= 1'b0;
            init_prev_addr3      <= '0;
            init_prev_val3       <= '0;
        end else if (!arch_state_captured3 && (cntr3 == 0)) begin
            init_prev_addr3      <= prev_addr_cpy3;
            init_prev_val3       <= prev_val_cpy3;
            arch_state_captured3 <= 1'b1;
        end
    end

    ASSUME_MATCH_PREV_ADDR: assume property (@(posedge clk)
                                             (arch_state_captured1 && arch_state_captured3)
                                             |-> final_prev_addr1 == init_prev_addr3);
    ASSUME_MATCH_PREV_VAL: assume property (@(posedge clk)
                                            (arch_state_captured1 && arch_state_captured3)
                                            |-> final_prev_val1 == init_prev_val3);

    // Constrain RAM copies to share identical contents at all times (read-only RAMs).
    genvar ram_idx;
    generate
        for (ram_idx = 0; ram_idx < 128; ram_idx++) begin : RAM_EQ
            ASSUME_RAM_EQ: assume property (@(posedge clk)
                                            ram_cpy1.ram[ram_idx] == ram_cpy3.ram[ram_idx]);
        end
    endgenerate

    // ------------------------------------------------------------------------
    // Functional observation capture (RGB + valid_pixel + read_addr)
    // ------------------------------------------------------------------------
    typedef struct packed {
        logic        valid_pixel;
        logic [8:0]  read_addr;
        logic [7:0]  r;
        logic [7:0]  g;
        logic [7:0]  b;
    } fc_obs_t;

    fc_obs_t fc_obs2;
    fc_obs_t fc_obs3;
    logic    fc_ready2;
    logic    fc_ready3;
    logic    capture_pending2;
    logic    capture_pending3;
    logic    auv_seen2;
    logic    auv_seen3;

    always_ff @(posedge clk) begin
        if (rst) begin
            auv_seen2        <= 1'b0;
            capture_pending2 <= 1'b0;
            fc_ready2        <= 1'b0;
            fc_obs2          <= '{default:'0};
        end else begin
            if (!auv_seen2 && apply_bmc2 && (cntr2 == i)) begin
                auv_seen2        <= 1'b1;
                capture_pending2 <= 1'b1;
            end
            if (capture_pending2) begin
                fc_obs2          <= '{valid_pixel: valid_pixel2,
                                      read_addr:  read_addr2,
                                      r:          r2,
                                      g:          g2,
                                      b:          b2};
                fc_ready2        <= 1'b1;
                capture_pending2 <= 1'b0;
            end
        end
    end

    always_ff @(posedge clk) begin
        if (rst) begin
            auv_seen3        <= 1'b0;
            capture_pending3 <= 1'b0;
            fc_ready3        <= 1'b0;
            fc_obs3          <= '{default:'0};
        end else begin
            if (!auv_seen3 && (cntr3 == 0)) begin
                auv_seen3        <= 1'b1;
                capture_pending3 <= 1'b1;
            end
            if (capture_pending3) begin
                fc_obs3          <= '{valid_pixel: valid_pixel3,
                                      read_addr:  read_addr3,
                                      r:          r3,
                                      g:          g3,
                                      b:          b3};
                fc_ready3        <= 1'b1;
                capture_pending3 <= 1'b0;
            end
        end
    end

    // ------------------------------------------------------------------------
    // Environmental assumptions for raster scanning and bounds
    // ------------------------------------------------------------------------
    ASSUME_VALID_BOUNDS: assume property (@(posedge clk) disable iff (rst)
                                          pix_valid2_in |-> (x2 < 11'd1280 && y2 < 10'd1024));

    ASSUME_X_PROGRESS: assume property (@(posedge clk) disable iff (rst)
                                        $past(pix_valid2_in) && ($past(x2) < 11'd1279)
                                        |-> (!pix_valid2_in || (x2 == $past(x2) + 11'd1)));

    ASSUME_X_WRAP: assume property (@(posedge clk) disable iff (rst)
                                    $past(pix_valid2_in) && ($past(x2) == 11'd1279)
                                    |-> (!pix_valid2_in || (x2 == 11'd0)));

    ASSUME_Y_HOLD: assume property (@(posedge clk) disable iff (rst)
                                    $past(pix_valid2_in) && ($past(x2) != 11'd1279)
                                    |-> (!pix_valid2_in || (y2 == $past(y2))));

    ASSUME_Y_PROGRESS: assume property (@(posedge clk) disable iff (rst)
                                        $past(pix_valid2_in) && ($past(x2) == 11'd1279) && ($past(y2) < 10'd1023)
                                        |-> (!pix_valid2_in || (y2 == $past(y2) + 10'd1)));

    ASSUME_Y_WRAP: assume property (@(posedge clk) disable iff (rst)
                                    $past(pix_valid2_in) && ($past(x2) == 11'd1279) && ($past(y2) == 10'd1023)
                                    |-> (!pix_valid2_in || (y2 == 10'd0)));

    // ------------------------------------------------------------------------
    // Functional correctness and idle correctness checks
    // ------------------------------------------------------------------------
    FC_MATCH: assert property (@(posedge clk)
                               (fc_ready2 && fc_ready3 && arch_state_captured1 && arch_state_captured3)
                               |-> (fc_obs2 == fc_obs3));

    IDLE_BLACK: assert property (@(posedge clk)
                                 (fc_ready2 && fc_ready3 && !auv_action.pix_valid)
                                 |-> ((fc_obs2.valid_pixel == 1'b0) &&
                                      (fc_obs3.valid_pixel == 1'b0) &&
                                      (fc_obs2.r == 8'h00) &&
                                      (fc_obs2.g == 8'h00) &&
                                      (fc_obs2.b == 8'h00) &&
                                      (fc_obs3.r == 8'h00) &&
                                      (fc_obs3.g == 8'h00) &&
                                      (fc_obs3.b == 8'h00)));

endmodule
