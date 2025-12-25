JC-DOS v1.4 personality conformance  
  
Expected behavior:  
- Runs a minimal JCOM in native and legacy personalities.  
- Unsupported tier requests fail deterministically.  
- Nested personality open/close does not leak sessions.  
- Forced RETMD failure injection returns a stable error.  
  
Outputs are deterministic and must be captured for transcript comparison. 
