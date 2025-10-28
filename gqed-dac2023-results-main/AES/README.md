# AES_abstracted<sup>1</sup> Example

This directory contains four buggy versions of a scaled down AES accelerator.  

### Directory Hierarchy

Each verification setup can be found in __bug\<i\>/__ directories. The __clean/__ directory contains the setup with the bugfree design.  

Each directory contains  

1. The verilog files of the design with __workload.v__ as top. The bug can be found in the original repository<sup>1</sup>.
2. __gqed.sv__ : the G-QED systemverilog module that interfaces with the deisgn and performs the universal *Functional Consistency* check.
3. __jasper\.tcl__ : contains the tcl file that may be sourced to run BMC on the design with _Cadence JasperGold_.
5. __memory_core\.flist__ : contains the list of verilog files parsed by _Cadence JasperGold_.

\$__jg -tcl jasper*\.tcl__\$ to run G-QED on _Cadence JasperGold_

### References
<sup>1</sup> "aqed-dac2020-results," https://github.com/upscale-project/aqed-dac2020-results/tree/master/AES_abstracted, 2020, [Online]. Accessed: December 2022.  
