clear -all

# Root of the Lab 5 harness + RTL.
set ROOT [file normalize [file join [pwd] "lab5_gqed-main"]]

# Analyze the harness and design sources.
# Add or replace wave_display.v with the student’s version as needed.
analyze -sv09 [list \
    $ROOT/gqed_wave_display.sv \
    $ROOT/lab5starterfiles/ram_1w2r.v \
    $ROOT/lab5starterfiles/wave_display.v \
    $ROOT/lab5starterfiles/ff_lib.v \
]

elaborate -disable_auto_bbox -top gqed_wave_display

clock clk
reset -expression rst

set_prove_orchestration on
set_engine_mode {Hp Ht Bm B L}

# Optional parameter overrides (uncomment to adjust bounds)
# set_parameter -design gqed_wave_display SEQ_LEN    24
# set_parameter -design gqed_wave_display RESP_BOUND 6

prove -bg -all
