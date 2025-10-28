clear -all
analyze -sv09 -f memory_core.flist 
elaborate -disable_auto_bbox -top gqed
clock clk
reset -expression rst
set_engine_mode {Bm B}
prove -bg -all

