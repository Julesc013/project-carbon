JC-DOS v2.0 PROFILE_MCU conformance  
  
Expected behavior:  
- DOS boots under PROFILE_MCU and emits deterministic transcript.  
- If storage is present: trivial file I/O works and a minimal JCOM runs.  
- If storage is absent: FS is treated as optional and tests are skipped.  
  
Run matrix:  
1) MCU profile build: make dos_conformance_v2_0  
2) Run SIM_REF with jc_bios_sim_ref_v2_0.rom and build/jcdos_v2_0.img  
  
Outputs are deterministic and must be captured for transcript comparison.  
