# Deflate<sup>1</sup> Example

This directory contains a buggy version of Deflate compression accelerator. It is a response bound bug. 

### Directory Hierarchy

The directory contains  

1. A single verilog file __deflate\_static.v__.
2. __rb_deflate_static.sv__ : the G-QED systemverilog module that interfaces with the deisgn and performs the universal *Response Bound* check.
3. __jasper\.tcl__ : contains the tcl file that may be sourced to run BMC on the design with _Cadence JasperGold_.
5. __flist_static\.f__ : contains the list of verilog files parsed by _Cadence JasperGold_.

\$__jg -tcl jasper*\.tcl__\$ to run G-QED on _Cadence JasperGold_

### References
<sup>1</sup> "HDL-deflate," https://github.com/tomtor/HDL-deflate, 2019, [Online]. Accessed: December 2022.  
