#ifndef JC_EE_H
#define JC_EE_H

#include "jc_error.h"
#include "jc_types.h"

#define JC_EE_ABI_MAJOR 1u
#define JC_EE_ABI_MINOR 0u

#define JC_EE_FLAG_DETERMINISTIC (1u << 0)

typedef enum {
  JC_EE_KIND_NONE = 0,
  JC_EE_KIND_CPM80 = 1,
  JC_EE_KIND_DOS86 = 2
} jc_ee_kind;

typedef struct {
  jc_u32 abi_major;
  jc_u32 abi_minor;
  jc_u32 flags;
  jc_ee_kind kind;
  const void *provider;
  void *ctx;
} jc_ee;

jc_error_t ee_open(jc_ee *ee, jc_ee_kind kind);
jc_error_t ee_load(jc_ee *ee, const char *path);
jc_error_t ee_run(jc_ee *ee);
jc_error_t ee_close(jc_ee *ee);

#endif /* JC_EE_H */
