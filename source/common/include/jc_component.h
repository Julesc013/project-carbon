#ifndef JC_COMPONENT_H
#define JC_COMPONENT_H

#include "jc_error.h"
#include "jc_types.h"

#define JC_COMPONENT_ID_PERF_CACHE 0x0001u
#define JC_COMPONENT_ID_PERF_FASTMEM 0x0002u
#define JC_COMPONENT_ID_CAI 0x0100u
#define JC_COMPONENT_ID_FPU 0x0101u
#define JC_COMPONENT_ID_DISPLAY 0x0200u
#define JC_COMPONENT_ID_EE_CPM80 0x1100u
#define JC_COMPONENT_ID_EE_DOS86 0x1101u
#define JC_COMPONENT_ID_PAL_CARBON 0x1200u
#define JC_COMPONENT_ID_PAL_Z80_STATIC 0x1201u
#define JC_COMPONENT_ID_PAL_ROMWBW 0x1202u
#define JC_COMPONENT_ID_PAL_PCBIOS 0x1203u
#define JC_COMPONENT_ID_PAL_UEFI 0x1204u

typedef struct {
  jc_u16 id;
  jc_u16 min_major;
  jc_u16 min_minor;
  jc_u16 max_major;
  jc_u16 max_minor;
} jc_component_dep;

typedef struct {
  jc_error_t (*init)(void);
  void (*shutdown)(void);
} jc_component_vtable;

typedef struct {
  jc_u16 id;
  jc_u16 version_major;
  jc_u16 version_minor;
  jc_u16 init_priority;
  const jc_component_dep *deps;
  jc_u16 dep_count;
  const jc_component_vtable *vtable;
  const char *name;
} jc_component_desc;

typedef struct {
  jc_u16 id;
  jc_u16 initialized;
  jc_error_t last_error;
} jc_component_state;

typedef int (*jc_component_allow_fn)(jc_u16 id, void *ctx);

const jc_component_desc *jc_component_find(const jc_component_desc *list,
                                           jc_u32 count,
                                           jc_u16 id);
int jc_component_is_ready(const jc_component_state *state,
                          jc_u32 count,
                          jc_u16 id);

jc_error_t jc_component_init_all(const jc_component_desc *list,
                                 jc_u32 count,
                                 jc_component_state *state);
jc_error_t jc_component_init_all_filtered(const jc_component_desc *list,
                                          jc_u32 count,
                                          jc_component_state *state,
                                          jc_component_allow_fn allow,
                                          void *ctx);

#endif /* JC_COMPONENT_H */
