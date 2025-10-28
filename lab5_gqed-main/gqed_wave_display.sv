// ---------------------------------------------------------------------------
//  G-QED harness for wave_display + RAM subsystem (Lab 5)
// ---------------------------------------------------------------------------
//  This harness instantiates two architectural copies of the design under
//  verification (DUV): a wave_display module driving a private instance of
//  the dual-port RAM. Copy #0 consumes a BMC-chosen sequence of commands,
//  while copy #1 replays the *same* command stream after a bounded temporal
//  shift (RESP_BOUND). We record the architectural outputs produced by the
//  fast copy and compare them against the delayed copy once the replay window
//  has elapsed.  When the copies operate in lockstep (delay == 0) we also
//  ensure their observable state and RAM contents remain equal, providing an
//  idle-correctness check. Functional-correctness is captured by asserting
//  that the delayed copy eventually reproduces the stored architectural
//  state for every command that originated from the real sequence.
//
//  The sequence format is intentionally simple: each slot captures the pixel
//  coordinates, whether the current pixel is valid, which buffer index to
//  read from, and an optional RAM write (address/data/enable). By allowing
//  writes in the same command stream we let the solver both initialise the
//  waveform memory and explore interesting interleavings of reads and writes.
//
//  The harness assumes:
//    * The command stream, number of active commands, and chosen delay are
//      held stable during a single proof attempt.
//    * Both RAM instances start with identical contents when reset is asserted.
//  Under these assumptions the properties below are sufficient for Jasper
//  to detect both FC and IC violations in the combined subsystem.
// ---------------------------------------------------------------------------

typedef struct packed {
    logic [10:0] x;             // horizontal pixel coordinate
    logic [9:0]  y;             // vertical pixel coordinate
    logic        pixel_valid;   // true when VGA controller marks this (x,y) as valid
    logic        read_index;    // selects which waveform buffer to read
    logic        write_enable;  // optional RAM write strobe
    logic [8:0]  write_addr;    // RAM address written when write_enable is high
    logic [7:0]  write_data;    // RAM data written when write_enable is high
} wave_cmd_t;

module gqed_wave_display
#(
    parameter int unsigned SEQ_LEN    = 32, // length of BMC-controlled command stream
    parameter int unsigned RESP_BOUND = 6   // maximum temporal skew between copies
)
(
    input  logic clk,
    input  logic rst,

    // BMC-provided command stream for copy #0 (fast copy).
    input  wave_cmd_t cmds [0:SEQ_LEN-1],

    // Number of valid entries in cmds. Remaining slots are ignored/treated as idle.
    input  logic [$clog2(SEQ_LEN+1)-1:0] num_ops,

    // Temporal skew (in cycles) between the two copies. Must be <= RESP_BOUND.
    input  logic [$clog2(RESP_BOUND+1)-1:0] delay_sel
);

    // Guard against pathological parameterisations that break bit-width maths.
    initial begin
        if (SEQ_LEN < 1) begin
            $fatal(1, "gqed_wave_display: SEQ_LEN must be >= 1");
        end
        if (RESP_BOUND < 1) begin
            $fatal(1, "gqed_wave_display: RESP_BOUND must be >= 1");
        end
    end

    // -----------------------------------------------------------------------
    //  Local typedefs / helper structs
    // -----------------------------------------------------------------------
    localparam int unsigned CMD_IDX_BITS = (SEQ_LEN > 1) ? $clog2(SEQ_LEN) : 1;

    typedef struct packed {
        logic [8:0] read_addr;
        logic       valid_pixel;
        logic [7:0] r;
        logic [7:0] g;
        logic [7:0] b;
    } wave_obs_t;

    // -----------------------------------------------------------------------
    //  Input constraints
    // -----------------------------------------------------------------------

    // Hold the command stream and configuration knobs constant throughout a run.
    assume_cmds_stable: assume property (@(posedge clk) rst || $stable(cmds));
    assume_ops_stable : assume property (@(posedge clk) rst || $stable(num_ops));
    assume_dly_stable : assume property (@(posedge clk) rst || $stable(delay_sel));

    // Sanity bounds that keep the solver within the harness envelope.
    assume_ops_bound  : assume property (@(posedge clk) num_ops <= SEQ_LEN);
    assume_delay_bound: assume property (@(posedge clk) delay_sel <= RESP_BOUND);

    // -----------------------------------------------------------------------
    //  Command scheduler for copy #0 (fast copy)
    // -----------------------------------------------------------------------

    logic [$clog2(SEQ_LEN+1)-1:0] issued;  // how many real commands have been consumed
    logic                          cmd_active;
    wave_cmd_t                     current_cmd;

    assign cmd_active = (issued < num_ops) && (issued < SEQ_LEN);

    always_comb begin
        if (cmd_active) begin
            current_cmd = cmds[issued[CMD_IDX_BITS-1:0]];
        end else begin
            current_cmd = '0;
        end
    end

    // Increment the issued counter while commands remain.
    always_ff @(posedge clk) begin
        if (rst) begin
            issued <= '0;
        end else if (cmd_active) begin
            if (issued < SEQ_LEN) begin
                issued <= issued + 1'b1;
            end
        end
    end

    // -----------------------------------------------------------------------
    //  Delay line for commands and architectural observations
    // -----------------------------------------------------------------------

    wave_cmd_t  cmd_fifo   [0:RESP_BOUND];
    logic       cmd_hist   [0:RESP_BOUND];
    wave_obs_t  obs_fifo   [0:RESP_BOUND];

    // Default zeros during reset to avoid spurious Xs.
    always_ff @(posedge clk) begin
        if (rst) begin
            for (int idx = 0; idx <= RESP_BOUND; idx++) begin
                cmd_fifo[idx] <= '0;
                cmd_hist[idx] <= 1'b0;
                obs_fifo[idx] <= '0;
            end
        end else begin
            cmd_fifo[0] <= current_cmd;
            cmd_hist[0] <= cmd_active;
            obs_fifo[0] <= '{
                read_addr   : rd_addr_fast,
                valid_pixel : valid_pix_fast,
                r           : r_fast,
                g           : g_fast,
                b           : b_fast
            };

            if (RESP_BOUND > 0) begin
                for (int idx = RESP_BOUND; idx > 0; idx--) begin
                    cmd_fifo[idx] <= cmd_fifo[idx-1];
                    cmd_hist[idx] <= cmd_hist[idx-1];
                    obs_fifo[idx] <= obs_fifo[idx-1];
                end
            end
        end
    end

    // Short-hands for the delayed copies.
    wave_cmd_t delayed_cmd;
    logic      delayed_cmd_is_real;
    assign delayed_cmd          = cmd_fifo[delay_sel];
    assign delayed_cmd_is_real  = cmd_hist[delay_sel];

    // -----------------------------------------------------------------------
    //  Copy #0 (fast) – wave_display + dual-port RAM
    // -----------------------------------------------------------------------

    logic [8:0] rd_addr_fast;
    logic [7:0] rd_data_fast;
    logic       valid_pix_fast;
    logic [7:0] r_fast, g_fast, b_fast;
    logic [7:0] unused_douta_fast;

    ram_1w2r #(.WIDTH(8), .DEPTH(9)) ram_fast (
        .clka   (clk),
        .wea    (current_cmd.write_enable),
        .addra  (current_cmd.write_addr),
        .dina   (current_cmd.write_data),
        .douta  (unused_douta_fast),
        .clkb   (clk),
        .addrb  (rd_addr_fast),
        .doutb  (rd_data_fast)
    );

    wave_display dut_fast (
        .clk          (clk),
        .reset        (rst),
        .x            (current_cmd.x),
        .y            (current_cmd.y),
        .valid        (current_cmd.pixel_valid),
        .read_value   (rd_data_fast),
        .read_index   (current_cmd.read_index),
        .read_address (rd_addr_fast),
        .valid_pixel  (valid_pix_fast),
        .r            (r_fast),
        .g            (g_fast),
        .b            (b_fast)
    );

    // -----------------------------------------------------------------------
    //  Copy #1 (delayed) – wave_display + dual-port RAM
    // -----------------------------------------------------------------------

    logic [8:0] rd_addr_slow;
    logic [7:0] rd_data_slow;
    logic       valid_pix_slow;
    logic [7:0] r_slow, g_slow, b_slow;
    logic [7:0] unused_douta_slow;

    ram_1w2r #(.WIDTH(8), .DEPTH(9)) ram_slow (
        .clka   (clk),
        .wea    (delayed_cmd.write_enable),
        .addra  (delayed_cmd.write_addr),
        .dina   (delayed_cmd.write_data),
        .douta  (unused_douta_slow),
        .clkb   (clk),
        .addrb  (rd_addr_slow),
        .doutb  (rd_data_slow)
    );

    wave_display dut_slow (
        .clk          (clk),
        .reset        (rst),
        .x            (delayed_cmd.x),
        .y            (delayed_cmd.y),
        .valid        (delayed_cmd.pixel_valid),
        .read_value   (rd_data_slow),
        .read_index   (delayed_cmd.read_index),
        .read_address (rd_addr_slow),
        .valid_pixel  (valid_pix_slow),
        .r            (r_slow),
        .g            (g_slow),
        .b            (b_slow)
    );

    // Ensure both memories have identical contents while reset is asserted.
    same_reset_state: assume property (@(posedge clk) rst |-> (ram_fast.RAM == ram_slow.RAM));

    // -----------------------------------------------------------------------
    //  Observable bundles and helper wires
    // -----------------------------------------------------------------------

    wave_obs_t obs_fast, obs_slow;

    assign obs_fast = '{
        read_addr   : rd_addr_fast,
        valid_pixel : valid_pix_fast,
        r           : r_fast,
        g           : g_fast,
        b           : b_fast
    };

    assign obs_slow = '{
        read_addr   : rd_addr_slow,
        valid_pixel : valid_pix_slow,
        r           : r_slow,
        g           : g_slow,
        b           : b_slow
    };

    // -----------------------------------------------------------------------
    //  Idle-Correctness: when both copies see the same inputs (no skew)
    //                    they must remain in lockstep.
    // -----------------------------------------------------------------------

    idle_correctness: assert property (@(posedge clk)
        !rst && (delay_sel == '0) |->
            (obs_fast == obs_slow) &&
            (ram_fast.RAM == ram_slow.RAM)
    );

    // -----------------------------------------------------------------------
    //  Functional-Correctness: the delayed copy must eventually reproduce
    //  the stored architectural observation of the fast copy for each real
    //  command in the stream (bounded by RESP_BOUND cycles).
    // -----------------------------------------------------------------------

    functional_correctness: assert property (@(posedge clk)
        !rst && delayed_cmd_is_real |->
            (obs_fifo[delay_sel] == obs_slow)
    );

    // Simple coverage to avoid vacuous proofs: demonstrate that a real
    // command flows through the delay line and triggers the FC checker.
    cover_replay: cover property (@(posedge clk)
        !rst && delayed_cmd_is_real && (delay_sel != '0)
    );

endmodule
