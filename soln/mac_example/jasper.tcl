clear -all
analyze -sv12 {mac.sv} 
analyze -sv12 {gqed_top.sv}
elaborate -bbox_mul 10000000 -top {gqed}
clock clk -factor 1 -phase 1
reset -expression {rst}
abstract -init_value -task {<embedded>} {c3.ACC}
prove -bg -task {<embedded>}
