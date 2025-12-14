Memory test program for use with SCMonitor.

This memory test is for systems with a full 64K of RAM and a mechanism
to page out the ROM.

The test repeats until the Escape key is pressed or a failure is detected.

Load the program into the target system by sending the hex file from a terminal program.

The code starts at $8000, so is started with the Monitor command "G 8000".

If a failure is detected, the memory location is written to address $8070/1.
