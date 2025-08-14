# Project Carbon

Family of computer designs.
Continued from the [Abacus 1](https://github.com/Julesc013/abacus-1) and [Abacus 2](https://github.com/Julesc013/abacus-2) projects.

## Schematics
[dATX_JC100_sch.pdf](https://github.com/Julesc013/project-carbon/blob/main/schematics/dATX_JC100_sch.pdf)
[dATX_JC100_sch_rev0.png](https://github.com/Julesc013/project-carbon/blob/main/schematics/dATX_JC100_sch_rev0.png)

## Directory Structure
(OUT OF DATE)
```
├── archive             Archived and old versions of files.
├── hardware            Hardware design and circuitry.
│   ├── case                Physical design of machine.
│   ├── cassette            Cassette tape data storage.
│   ├── chipset             Northbridge, southbridge, I/O, wait states, etc.
│   ├── floppy              Floppy diskette data storage.
│   ├── instructions        Instruction set architecture.
│   ├── interrupts          Interrupt tables and circuits.
│   ├── memory              Memory maps, wait states, DMA, etc.
│   ├── printer             Parallel ports and printer communication.
│   ├── serial              Serial ports and teletype communication.
│   ├── todo                Todo lists and general notes.
│   └── video               Video text and graphics output.
├── info                General project information and metadata.
│   ├── datasheets          Relevant datasheets.
│   ├── manual              User and technical manuals for the system.
│   └── parts               Parts lists and records.
├── schematics          Schematics and technical drawings.
├── simulation          Virtual simulation of processor.
│   ├── digital             Implementation in Digital.
│   └── logisim             Implementation in Logisim Evolution.   
└── software            Software, firmware, drivers, operating systems, etc.
    ├── assembler           Assembler and linker.
    ├── basic               Implementation of Microsoft 8K BASIC.
    ├── bios                Disk loaders, bootstrappers, system calls, etc.
    ├── compiler            Compiler for K&R C.
    └── executables         Executable file formats and disk formats.
```

