#include "jc_component.h"

static int jc_component_version_in_range(const jc_component_desc *desc,
                                         const jc_component_dep *dep) {
  if (!desc || !dep) {
    return 0;
  }
  if (desc->version_major < dep->min_major) {
    return 0;
  }
  if (desc->version_major == dep->min_major &&
      desc->version_minor < dep->min_minor) {
    return 0;
  }
  if (desc->version_major > dep->max_major) {
    return 0;
  }
  if (desc->version_major == dep->max_major &&
      desc->version_minor > dep->max_minor) {
    return 0;
  }
  return 1;
}

const jc_component_desc *jc_component_find(const jc_component_desc *list,
                                           jc_u32 count,
                                           jc_u16 id) {
  jc_u32 i;
  if (!list) {
    return 0;
  }
  for (i = 0; i < count; ++i) {
    if (list[i].id == id) {
      return &list[i];
    }
  }
  return 0;
}

int jc_component_is_ready(const jc_component_state *state,
                          jc_u32 count,
                          jc_u16 id) {
  jc_u32 i;
  if (!state) {
    return 0;
  }
  for (i = 0; i < count; ++i) {
    if (state[i].id == id) {
      return state[i].initialized != 0u;
    }
  }
  return 0;
}

static int jc_component_deps_ok(const jc_component_desc *list,
                                jc_u32 count,
                                const jc_component_state *state,
                                const jc_component_desc *desc) {
  jc_u32 i;
  if (!desc || !state) {
    return 0;
  }
  for (i = 0; i < desc->dep_count; ++i) {
    const jc_component_dep *dep = &desc->deps[i];
    const jc_component_desc *found = jc_component_find(list, count, dep->id);
    if (!found) {
      return 0;
    }
    if (!jc_component_version_in_range(found, dep)) {
      return 0;
    }
    if (!jc_component_is_ready(state, count, dep->id)) {
      return 0;
    }
  }
  return 1;
}

static int jc_component_is_optional_error(jc_error_t err) {
  return err == JC_E_DEV_UNSUPPORTED || err == JC_E_DEV_NOT_FOUND;
}

jc_error_t jc_component_init_all(const jc_component_desc *list,
                                 jc_u32 count,
                                 jc_component_state *state) {
  return jc_component_init_all_filtered(list, count, state, 0, 0);
}

jc_error_t jc_component_init_all_filtered(const jc_component_desc *list,
                                          jc_u32 count,
                                          jc_component_state *state,
                                          jc_component_allow_fn allow,
                                          void *ctx) {
  jc_u32 i;
  if (!list || !state) {
    return JC_E_INTERNAL_ASSERT;
  }
  for (i = 0; i < count; ++i) {
    state[i].id = list[i].id;
    state[i].initialized = 0;
    state[i].last_error = JC_E_OK;
  }
  for (i = 0; i < count; ++i) {
    jc_error_t err = JC_E_OK;
    const jc_component_desc *desc = &list[i];
    if (allow && !allow(desc->id, ctx)) {
      state[i].last_error = JC_E_DEV_UNSUPPORTED;
      continue;
    }
    if (!jc_component_deps_ok(list, count, state, desc)) {
      state[i].last_error = JC_E_DEV_UNSUPPORTED;
      continue;
    }
    if (desc->vtable && desc->vtable->init) {
      err = desc->vtable->init();
    }
    state[i].last_error = err;
    if (err == JC_E_OK) {
      state[i].initialized = 1;
    } else if (jc_component_is_optional_error(err)) {
      state[i].initialized = 0;
    } else {
      return err;
    }
  }
  return JC_E_OK;
}
