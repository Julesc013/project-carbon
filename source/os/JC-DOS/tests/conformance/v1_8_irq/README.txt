JC-DOS v1.8 IRQ conformance  
  
Expected behavior:  
- Polling and IRQ builds emit identical transcripts.  
- Spurious IRQ injection does not alter output or hang.  
- Missing IRQ capability falls back to polling.  
  
Run matrix:  
1) Polling mode: make dos_conformance_v1_8  
2) IRQ mode (spurious injected): make dos_conformance_v1_8_irq  
3) Optional negative (IRQ enabled but no caps):  
   make sim_ref_rom SIM_REF_DEFS="-DJC_CFG_ENABLE_IRQ=1"  
   Run SIM_REF with jc_bios_sim_ref.rom and build/jcdos_v1_8.img.  
  
Outputs are deterministic and must be captured for transcript comparison.  
