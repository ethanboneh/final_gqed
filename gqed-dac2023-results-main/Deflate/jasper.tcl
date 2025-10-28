clear -all
analyze -sv09 -f flist_static.f
elaborate -disable_auto_bbox -top gqed
clock clk
reset -expression reset
autoprove
