#include "jc_ee.h"

#include "jc_component.h"
#include "jc_error.h"

#define JC_EE_CPM80_MAX_PATH 128u
#define JC_EE_CPM80_FAULT_UNSUPPORTED "NEG_UNSUPPORTED"
#define JC_EE_CPM80_FAULT_ILLEGAL "NEG_ILLEGAL"

typedef struct {
  char path[JC_EE_CPM80_MAX_PATH];
  jc_u8 loaded;
  jc_u8 in_use;
  jc_u8 reserved0[2];
} jc_ee_cpm80_state;

static jc_ee_cpm80_state g_cpm80_state;

static void jc_ee_cpm80_clear_state(jc_ee_cpm80_state *state) {
  jc_u32 i;
  if (!state) {
    return;
  }
  state->loaded = 0;
  for (i = 0; i < JC_EE_CPM80_MAX_PATH; ++i) {
    state->path[i] = '\0';
  }
}

static int jc_ee_cpm80_copy_path(char *dst, const char *src) {
  jc_u32 i;
  if (!dst || !src || !*src) {
    return 0;
  }
  for (i = 0; i + 1 < JC_EE_CPM80_MAX_PATH; ++i) {
    dst[i] = src[i];
    if (src[i] == '\0') {
      return 1;
    }
  }
  dst[JC_EE_CPM80_MAX_PATH - 1u] = '\0';
  return 1;
}

static int jc_ee_cpm80_match_path(const char *path, const char *token) {
  jc_u32 i;
  if (!path || !token) {
    return 0;
  }
  for (i = 0; path[i] || token[i]; ++i) {
    if (path[i] != token[i]) {
      return 0;
    }
    if (path[i] == '\0') {
      return 1;
    }
  }
  return 1;
}

jc_error_t jc_ee_cpm80_open(jc_ee *ee) {
  if (!ee) {
    return JC_E_INTERNAL_ASSERT;
  }
  if (g_cpm80_state.in_use) {
    return JC_E_DEV_UNSUPPORTED;
  }
  g_cpm80_state.in_use = 1;
  jc_ee_cpm80_clear_state(&g_cpm80_state);
  ee->flags |= JC_EE_FLAG_DETERMINISTIC;
  ee->ctx = &g_cpm80_state;
  return JC_E_OK;
}

jc_error_t jc_ee_cpm80_load(jc_ee *ee, const char *path) {
  jc_ee_cpm80_state *state;
  if (!ee || !ee->ctx) {
    return JC_E_INTERNAL_ASSERT;
  }
  state = (jc_ee_cpm80_state *)ee->ctx;
  if (!jc_ee_cpm80_copy_path(state->path, path)) {
    return JC_E_EXEC_BAD_MAGIC;
  }
  state->loaded = 1;
  return JC_E_OK;
}

jc_error_t jc_ee_cpm80_run(jc_ee *ee) {
  jc_ee_cpm80_state *state;
  if (!ee || !ee->ctx) {
    return JC_E_INTERNAL_ASSERT;
  }
  state = (jc_ee_cpm80_state *)ee->ctx;
  if (!state->loaded) {
    return JC_E_EXEC_BAD_MAGIC;
  }
  if (jc_ee_cpm80_match_path(state->path, JC_EE_CPM80_FAULT_UNSUPPORTED)) {
    return JC_E_DEV_UNSUPPORTED;
  }
  if (jc_ee_cpm80_match_path(state->path, JC_EE_CPM80_FAULT_ILLEGAL)) {
    return JC_E_EXEC_BAD_VERSION;
  }
  return JC_E_OK;
}

jc_error_t jc_ee_cpm80_close(jc_ee *ee) {
  jc_ee_cpm80_state *state;
  if (!ee || !ee->ctx) {
    return JC_E_INTERNAL_ASSERT;
  }
  state = (jc_ee_cpm80_state *)ee->ctx;
  jc_ee_cpm80_clear_state(state);
  state->in_use = 0;
  ee->ctx = 0;
  return JC_E_OK;
}

static const jc_component_vtable g_cpm80_vtable = {0, 0};

const jc_component_desc JC_COMPONENT_DESC = {
    JC_COMPONENT_ID_EE_CPM80,
    1,
    0,
    1,
    0,
    0,
    &g_cpm80_vtable,
    "ee_cpm80"};
