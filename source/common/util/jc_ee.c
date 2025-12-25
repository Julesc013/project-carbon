#include "jc_ee.h"

typedef struct {
  jc_ee_kind kind;
  const char *name;
  jc_error_t (*open)(jc_ee *ee);
  jc_error_t (*load)(jc_ee *ee, const char *path);
  jc_error_t (*run)(jc_ee *ee);
  jc_error_t (*close)(jc_ee *ee);
} jc_ee_provider;

jc_error_t jc_ee_cpm80_open(jc_ee *ee);
jc_error_t jc_ee_cpm80_load(jc_ee *ee, const char *path);
jc_error_t jc_ee_cpm80_run(jc_ee *ee);
jc_error_t jc_ee_cpm80_close(jc_ee *ee);

jc_error_t jc_ee_dos86_open(jc_ee *ee);
jc_error_t jc_ee_dos86_load(jc_ee *ee, const char *path);
jc_error_t jc_ee_dos86_run(jc_ee *ee);
jc_error_t jc_ee_dos86_close(jc_ee *ee);

static const jc_ee_provider g_providers[] = {
    {JC_EE_KIND_CPM80, "ee_cpm80", jc_ee_cpm80_open, jc_ee_cpm80_load,
     jc_ee_cpm80_run, jc_ee_cpm80_close},
    {JC_EE_KIND_DOS86, "ee_dos86", jc_ee_dos86_open, jc_ee_dos86_load,
     jc_ee_dos86_run, jc_ee_dos86_close},
};

static void jc_ee_zero(void *ptr, jc_u32 len) {
  jc_u8 *out = (jc_u8 *)ptr;
  while (len--) {
    *out++ = 0;
  }
}

static const jc_ee_provider *jc_ee_find_provider(jc_ee_kind kind) {
  jc_u32 i;
  for (i = 0; i < (jc_u32)(sizeof(g_providers) / sizeof(g_providers[0])); ++i) {
    if (g_providers[i].kind == kind) {
      return &g_providers[i];
    }
  }
  return 0;
}

jc_error_t ee_open(jc_ee *ee, jc_ee_kind kind) {
  const jc_ee_provider *provider;
  jc_error_t err;
  if (!ee) {
    return JC_E_INTERNAL_ASSERT;
  }
  jc_ee_zero(ee, sizeof(*ee));
  ee->abi_major = JC_EE_ABI_MAJOR;
  ee->abi_minor = JC_EE_ABI_MINOR;
  ee->kind = kind;
  provider = jc_ee_find_provider(kind);
  if (!provider) {
    return JC_E_DEV_UNSUPPORTED;
  }
  ee->provider = provider;
  if (provider->open) {
    err = provider->open(ee);
    if (err != JC_E_OK) {
      ee->provider = 0;
      return err;
    }
  }
  return JC_E_OK;
}

jc_error_t ee_load(jc_ee *ee, const char *path) {
  const jc_ee_provider *provider;
  if (!ee || !ee->provider) {
    return JC_E_INTERNAL_ASSERT;
  }
  provider = (const jc_ee_provider *)ee->provider;
  if (!provider->load) {
    return JC_E_DEV_UNSUPPORTED;
  }
  return provider->load(ee, path);
}

jc_error_t ee_run(jc_ee *ee) {
  const jc_ee_provider *provider;
  if (!ee || !ee->provider) {
    return JC_E_INTERNAL_ASSERT;
  }
  provider = (const jc_ee_provider *)ee->provider;
  if (!provider->run) {
    return JC_E_DEV_UNSUPPORTED;
  }
  return provider->run(ee);
}

jc_error_t ee_close(jc_ee *ee) {
  const jc_ee_provider *provider;
  jc_error_t err;
  if (!ee) {
    return JC_E_INTERNAL_ASSERT;
  }
  if (!ee->provider) {
    return JC_E_OK;
  }
  provider = (const jc_ee_provider *)ee->provider;
  err = JC_E_OK;
  if (provider->close) {
    err = provider->close(ee);
  }
  ee->provider = 0;
  return err;
}
