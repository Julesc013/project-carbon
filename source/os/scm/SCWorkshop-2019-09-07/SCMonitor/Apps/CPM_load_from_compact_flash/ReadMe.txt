CP/M loader 

This app loads CP/M from a compact flash card.

It runs from SCMonitor, but once loaded uses all its own hardware drivers.

Hardware must provide paging out of ROM so RAM is available at the bottom of memory.

Based on code by Grant Searle's.

Files:

SCMon_CPM_loader.asm
Source code for Z80 CP/M loader app, with code starting at $8000.

SCMon_CPM_loader_code8000.hex
Assembled code for Z80 CP/M loader.

SCMon_CPM_loader_Z180_S5.asm
Source code for Z180 CP/M loader app, with code starting at $8000.
This version is for SC111 Z180 CPU module or compatible

SCMon_CPM_loader_Z180_S5_code8000.hex
Assembled code for Z180 CP/M loader.
This version is for SC111 Z180 CPU module or compatible


Origins:

Grant's original - monitor.asm
Grant Searle's boot monitor source code.

Grant's original - MONITOR.HEX
Grant Searles boot monitor, assembled.

