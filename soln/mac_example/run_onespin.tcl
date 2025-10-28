#clear existing design, if any
clear_design;
#read/analyze the design files
read_verilog -sv  {mac.sv gqed_top.sv};
#elaborate the design, compile, set clock spec and define a reset sequence
elaborate -top {gqed};
compile ; set_clock_spec {{clk {type wave period 2 pulse_duration 1 pulse_offset 0}}}; set_reset_sequence {rst=1};
set_mode mv

#check the assertions and cover properties
check -all [get_checks]