#ifndef JC_DOS_HANDOFF_H
#define JC_DOS_HANDOFF_H

#include "jc_types.h"

#define JC_DOS_HANDOFF_V1_SIGNATURE 0x534F444Au /* "JDOS" */
#define JC_DOS_HANDOFF_V1_VERSION 1u

typedef struct {
  jc_u32 signature;
  jc_u16 version;
  jc_u16 size_bytes;
  jc_u32 flags;
  jc_u32 tpa_base;
  jc_u32 tpa_size;
  jc_u32 reserved0;
  jc_u64 capset_ptr;
  jc_u64 bdt_ptr;
  jc_u64 services_ptr;
  jc_u32 reserved1;
  jc_u32 reserved2;
} jc_dos_handoff_v1;

#endif /* JC_DOS_HANDOFF_H */
