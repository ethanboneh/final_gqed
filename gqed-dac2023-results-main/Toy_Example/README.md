# Toy_Example

This directory contains a small toy 3-stage pipeline to illustrate the *G-QED* implementation (not included in the paper). The files are -

1. __pipe\_clean.v__ : The clean version of the design in verilog.
2. __pipe\_bug.v__ : Design with the bug (commented).
3. __gqed.sv__ : The G-QED systemverilog module that interfaces with the deisgn and perform universal *Functional Consistency* check of the two actions.
4. __jasper_clean.tcl__ : contains the tcl file that may be sourced to run BMC on the clean design with _Cadence JasperGold_.
5. __jasper_buggy.tcl__ : to run BMC on the buggy design with _Cadence JasperGold_.

\$__jg -tcl jasper\_\*\.tcl__\$ to run G-QED on _Cadence JasperGold_
