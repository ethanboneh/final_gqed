clear_design;
read_verilog -version sv2009 {  ./rtl_bug/doublebuffer_control_unq1.sv 
				./rtl_bug/fifo_control_unq1.sv  
				./rtl_bug/linebuffer_control_unq1.sv 
				./rtl_bug/memory_core.sv  
				./rtl_bug/mem_unq1.v  
				./rtl_bug/sram_control_unq1.sv  
				./rtl_bug/sram_stub_unq1.v }
read_verilog -version sv2009 gqed_golden.sv
elaborate -top gqed

compile ; set_clock_spec {{clk {type wave period 2 pulse_duration 1 pulse_offset 0}}}; set_reset_sequence {rst=1};
set_mode mv

#check the assertions and cover properties
check -all [get_checks] -orchestrator questa



