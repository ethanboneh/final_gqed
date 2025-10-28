clear -all
analyze -sv09 -f memory_core_clean.flist 
analyze -sv09 gqed_golden.sv
elaborate -disable_auto_bbox -top gqed
clock clk
reset -expression rst
set_prove_orchestration on
set_engine_mode {Hp Ht Bm B L}
prove -bg -all
