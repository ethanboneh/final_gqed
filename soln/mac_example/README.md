This folder contains the GQED setup for a simple 2 stage multiply and accumulate unit. 

**Actions and Architectural State:**

The design has one architectural state (accumulator register ACC) and two actions: 

|Action|`in_action` value|Arch State|Output|
|----|----|----|---|
|SETVAL|0|`ACC = {in_data_a, in_data_b}`|`out_data = {in_data_a, in_data_b}`|
|MAC|1|`ACC = ACC + in_data_a * in_data_b`|`out_data = ACC + in_data_a * in_data_b`|

**Interface Protocol and Response Bound:**

The design interface protocl is based on a single valid bit (`in_valid`). Only if `in_valid` is high, input action and data is captured as a valid input. 
The response bound (the upper bound clock cycles to execute an action) is 3 clock cycles. 

**How to run the experiment?**

To run the experiment, excute `jaspergold jasper.tcl` in the terminal.
The design contains a bug which you can inspect it in Jaspergold GUI. 
If you change the design or the property, in order to re-run the proofs you should execute `source japser.tcl` in Jaspergold command prompt.








