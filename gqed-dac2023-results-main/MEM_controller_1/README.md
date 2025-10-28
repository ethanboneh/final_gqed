# MEM_Controller_1<sup>1</sup> Example

This directory contains two buggy versions of a memory controller running in a particular mode (sram mode). 

### Directory Hierarchy

Each verification setup can be found in __bug\<i\>/__ directories. The __clean/__ directory contains the setup with the bugfree design.  

Each directory contains  

1. The verilog files of the design with __memory\_core.v__ as top. The buggy lines are commented as BUG.
2. __gqed.sv__ : the G-QED systemverilog module that interfaces with the deisgn and performs the universal *Functional Consistency* check.
3. __jasper\.tcl__ : contains the tcl file that may be sourced to run BMC on the design with _Cadence JasperGold_.
5. __memory_core\.flist__ : contains the list of verilog files parsed by _Cadence JasperGold_.

\$__jg -tcl jasper*\.tcl__\$ to run G-QED on _Cadence JasperGold_

### References
<sup>1</sup> "garnet," https://github.com/StanfordAHA/garnet, 2019, [Online]. Accessed: December 2022.  
