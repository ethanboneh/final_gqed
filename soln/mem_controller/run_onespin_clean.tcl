clear_design;
read_verilog  -version sv2009 { ./rtl_clean/doublebuffer_control_unq1.sv 
				./rtl_clean/fifo_control_unq1.sv 
				./rtl_clean/linebuffer_control_unq1.sv 
				./rtl_clean/memory_core.sv  
				./rtl_clean/mem_unq1.v  
				./rtl_clean/sram_control_unq1.sv  
				./rtl_clean/sram_stub_unq1.v }
read_verilog -version sv2009 gqed_golden.sv
elaborate -top gqed
compile ; set_clock_spec {{clk {type wave period 2 pulse_duration 1 pulse_offset 0}}}; set_reset_sequence {rst=1};
set_mode mv

#check the assertions and cover properties
check -all [get_checks] -orchestrator questa