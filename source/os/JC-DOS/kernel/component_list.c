#include "component_list.h"

#include "cache_blk.h"
#include "cai_init.h"
#include "display_init.h"
#include "handoff.h"
#include "jc_config.h"
#include "jc_fastmem.h"
#include "jc_profile.h"

static jc_error_t jc_component_init_fastmem(void) {
  jc_fastmem_init(JC_CFG_FASTMEM_CAPS);
  if (JC_CFG_ENABLE_FASTMEM == 0) {
    return JC_E_DEV_UNSUPPORTED;
  }
  return JC_E_OK;
}

static jc_error_t jc_component_init_cache(void) {
  return jc_cache_blk_init();
}

static jc_error_t jc_component_init_display(void) {
  return jc_dos_display_init();
}

static jc_error_t jc_component_init_cai(void) {
  return jc_dos_cai_init();
}

static jc_error_t jc_component_init_fpu(void) {
  return jc_dos_fpu_init();
}

static const jc_component_vtable jc_vtable_fastmem = {jc_component_init_fastmem,
                                                      0};
static const jc_component_vtable jc_vtable_cache = {jc_component_init_cache, 0};
static const jc_component_vtable jc_vtable_display = {jc_component_init_display,
                                                      0};
static const jc_component_vtable jc_vtable_cai = {jc_component_init_cai, 0};
static const jc_component_vtable jc_vtable_fpu = {jc_component_init_fpu, 0};

static const jc_component_desc g_components[] = {
    {JC_COMPONENT_ID_PERF_FASTMEM, 1, 1, 10, 0, 0, &jc_vtable_fastmem,
     "perf_fastmem"},
    {JC_COMPONENT_ID_PERF_CACHE, 1, 1, 20, 0, 0, &jc_vtable_cache, "perf_cache"},
    {JC_COMPONENT_ID_DISPLAY, 1, 3, 25, 0, 0, &jc_vtable_display, "display"},
    {JC_COMPONENT_ID_CAI, 1, 2, 30, 0, 0, &jc_vtable_cai, "cai"},
    {JC_COMPONENT_ID_FPU, 1, 2, 40, 0, 0, &jc_vtable_fpu, "fpu"},
};

#define JC_DOS_COMPONENT_COUNT \
  (jc_u32)(sizeof(g_components) / sizeof(g_components[0]))

static jc_component_state g_component_state[JC_DOS_COMPONENT_COUNT];

static int jc_dos_component_allowed(jc_u16 id, void *ctx) {
  (void)ctx;
  const jc_profile_policy *policy = jc_dos_profile_policy();
  if (!policy) {
    return 1;
  }
  switch (id) {
    case JC_COMPONENT_ID_PERF_CACHE:
      return jc_profile_allows_subsys(policy, JC_PROFILE_SUBSYS_CACHE);
    case JC_COMPONENT_ID_PERF_FASTMEM:
      return jc_profile_allows_subsys(policy, JC_PROFILE_SUBSYS_FASTMEM);
    case JC_COMPONENT_ID_DISPLAY:
      return jc_profile_allows_subsys(policy, JC_PROFILE_SUBSYS_DISPLAY);
    case JC_COMPONENT_ID_CAI:
      return jc_profile_allows_subsys(policy, JC_PROFILE_SUBSYS_CAI);
    case JC_COMPONENT_ID_FPU:
      return jc_profile_allows_subsys(policy, JC_PROFILE_SUBSYS_FPU);
    default:
      return 1;
  }
}

jc_error_t jc_dos_components_init(void) {
  return jc_component_init_all_filtered(g_components, JC_DOS_COMPONENT_COUNT,
                                        g_component_state,
                                        jc_dos_component_allowed,
                                        0);
}

int jc_dos_component_ready(jc_u16 id) {
  return jc_component_is_ready(g_component_state, JC_DOS_COMPONENT_COUNT, id);
}
