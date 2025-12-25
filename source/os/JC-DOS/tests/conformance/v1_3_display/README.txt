JC-DOS v1.3 display conformance

Expected behavior:
- Uses VT100 by default.
- If a local display backend is present and enabled, runs a layout test and
  prints DISPLAY_HASH with the shadow buffer CRC.
- If no local display backend is present, prints DISPLAY_HASH NONE.
- DISPLAY_BACKEND reports the active backend name.

Outputs are deterministic and must be captured for transcript comparison.
