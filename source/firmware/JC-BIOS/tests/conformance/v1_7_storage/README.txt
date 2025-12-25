JC-BIOS v1.7 storage conformance  
  
Expected behavior:  
- Normal read/write succeeds with no retries required.  
- Injected transient timeout retries and succeeds.  
- Injected persistent timeout returns a deterministic error.  
- Stress file cycles leave the directory hash unchanged.  
  
Outputs are deterministic and must be captured for transcript comparison. 
