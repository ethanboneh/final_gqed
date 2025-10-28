# FIFO<sup>1</sup> Example

This directory contains five buggy versions of FIFO configuration of a memory controller. 

### Directory Hierarchy

Each verification setup can be found in __\*bug\<i\>/__ directories. The __clean/__ directory contains the setup with the bugfree design. __new_bug\<i\>/__ denote the bugs missed by traditional verification. The bugs in __new_bug1__, __new_bug2__ and __new_bug3__ correspond to faulty empty, full signals and faulty circular FIFO implementation respectively.

Each directory contains  

1. The verilog files of the design with __memory\_core.v__ as top. __step1__, __step2__, __step3__, __step6__ and __step9__ from the original repository correspond to __bug1__, __new_bug1__, __new_bug2__, __bug2__ and __new_bug3__ respectively.
2. __gqed.sv__ : the G-QED systemverilog module that interfaces with the deisgn and performs the universal *Functional Consistency* check.
3. __jasper\.tcl__ : contains the tcl file that may be sourced to run BMC on the design with _Cadence JasperGold_.
5. __memory_core\.flist__ : contains the list of verilog files parsed by _Cadence JasperGold_.

\$__jg -tcl jasper*\.tcl__\$ to run G-QED on _Cadence JasperGold_

### References
<sup>1</sup> "aqed-dac2020-results," https://github.com/upscale-project/aqed-dac2020-results/tree/master/Memory_Controller_Case_Study/FIFO, 2020, [Online]. Accessed: December 2022.  
