# Stream_Cipher<sup>1</sup> Example

This directory contains a stream cipher built around an AES engine. A bug was detected by their verification but the fix was buggy. G-QED could catch both the previously detected bug as well as detect the fix to be buggy. The files are -

### Directory Hierarchy

Each verification setup can be found in __bug/__ and __new_bug/__ directories.  

1. The verilog files of the design with __aes\_top.v__ as top. The buggy line is commented as BUG.
2. __gqed.sv__ : The G-QED systemverilog module that interfaces with the deisgn and performs the universal *Functional Consistency* check.
3.  __jasper\.tcl__ : contains the tcl file that may be sourced to run BMC on the design with _Cadence JasperGold_.
4. __aes.flist__ : contains the list of verilog files parsed by _Cadence JasperGold_.

\$__jg -tcl jasper\*\_.tcl__\$ to run G-QED on _Cadence JasperGold_

### References
<sup>1</sup> "IMDB-Archive," https://github.com/PrincetonUniversity/IMDb-Archive, 2017, [Online]. Accessed: December 2022.  
