#include "handoff.h"

#include "bios_services.h"
#include "component_list.h"
#include "dos_conformance.h"
#include "exec_jcom.h"
#include "fs_api.h"
#include "jc_contracts_autogen.h"
#include "jc_dos_util.h"
#include "jc_profile.h"
#include "log.h"
#include "mem_arena.h"
#include "panic.h"
#include "shell.h"

typedef struct {
  const jc_dos_handoff_v1 *handoff;
  const jc_bios_services_v1 *services;
  const jc_capset_v1 *capset;
  const jc_bdt_header_v1 *bdt;
  const jc_profile_policy *profile;
  jc_u32 tpa_base;
  jc_u32 tpa_size;
} jc_dos_context;

static jc_dos_context g_ctx;

static const void *jc_dos_ptr_from_u64(jc_u64 ptr) {
  if (ptr.hi != 0u || ptr.lo == 0u) {
    return 0;
  }
  return (const void *)(unsigned long)ptr.lo;
}

jc_error_t jc_dos_handoff_init(const jc_dos_handoff_v1 *handoff) {
  const jc_bios_services_v1 *services;
  const jc_capset_v1 *capset;
  const jc_bdt_header_v1 *bdt;
  jc_error_t err;

  if (!handoff) {
    return JC_E_INTERNAL_ASSERT;
  }
  if (handoff->signature != JC_DOS_HANDOFF_V1_SIGNATURE) {
    return JC_E_BOOT_BSP_BAD_SIGNATURE;
  }
  if (handoff->version != JC_DOS_HANDOFF_V1_VERSION ||
      handoff->size_bytes != sizeof(jc_dos_handoff_v1)) {
    return JC_E_BOOT_BSP_BAD_SIGNATURE;
  }
  if (handoff->tpa_base == 0u || handoff->tpa_size == 0u) {
    return JC_E_BOOT_UNSUPPORTED_PROFILE;
  }

  services = (const jc_bios_services_v1 *)jc_dos_ptr_from_u64(
      handoff->services_ptr);
  capset = (const jc_capset_v1 *)jc_dos_ptr_from_u64(handoff->capset_ptr);
  bdt = (const jc_bdt_header_v1 *)jc_dos_ptr_from_u64(handoff->bdt_ptr);
  if (!services || !capset || !bdt) {
    return JC_E_DISCOVERY_BAD_POINTER;
  }

  err = jc_bios_services_init(services);
  if (err != JC_E_OK) {
    return err;
  }

  if (capset->signature != JC_MAGIC_CAPSET) {
    return JC_E_DISCOVERY_BAD_SIGNATURE;
  }
  if (capset->version != JC_CAPSET_V1_VERSION ||
      capset->size_bytes < JC_CAPSET_V1_SIZE) {
    return JC_E_DISCOVERY_BAD_VERSION;
  }
  if (bdt->signature != JC_MAGIC_BDT) {
    return JC_E_BDT_BAD_SIGNATURE;
  }
  if (bdt->header_version != JC_BDT_HEADER_V1_VERSION) {
    return JC_E_BDT_BAD_VERSION;
  }

  jc_dos_memset(&g_ctx, 0, sizeof(g_ctx));
  g_ctx.handoff = handoff;
  g_ctx.services = services;
  g_ctx.capset = capset;
  g_ctx.bdt = bdt;
  g_ctx.profile = jc_profile_get(capset->profile_id);
  if (!g_ctx.profile) {
    return JC_E_BOOT_UNSUPPORTED_PROFILE;
  }
  g_ctx.tpa_base = handoff->tpa_base;
  g_ctx.tpa_size = handoff->tpa_size;
  return JC_E_OK;
}

const jc_bios_services_v1 *jc_dos_services(void) {
  return g_ctx.services;
}

const jc_capset_v1 *jc_dos_capset(void) {
  return g_ctx.capset;
}

const jc_bdt_header_v1 *jc_dos_bdt(void) {
  return g_ctx.bdt;
}

const jc_profile_policy *jc_dos_profile_policy(void) {
  return g_ctx.profile;
}

jc_u32 jc_dos_tpa_base(void) {
  return g_ctx.tpa_base;
}

jc_u32 jc_dos_tpa_size(void) {
  return g_ctx.tpa_size;
}

jc_u8 jc_dos_entry(const jc_dos_handoff_v1 *handoff) {
  jc_error_t err;

  err = jc_dos_handoff_init(handoff);
  if (err != JC_E_OK) {
    jc_dos_panic(err);
    return (jc_u8)err;
  }

  jc_dos_mem_init();
  err = jc_dos_components_init();
  if (err != JC_E_OK) {
    jc_dos_panic(err);
    return (jc_u8)err;
  }

#if defined(JC_DOS_CONFORMANCE_V0_7)
  jc_dos_conformance_v0_7();
  for (;;)
    ;
#elif defined(JC_DOS_CONFORMANCE_V0_8)
  jc_dos_conformance_v0_8();
  for (;;)
    ;
#elif defined(JC_DOS_CONFORMANCE_V0_9)
  jc_dos_conformance_v0_9();
  for (;;)
    ;
#elif defined(JC_DOS_CONFORMANCE_V1_0)
  jc_dos_conformance_v1_0();
  for (;;)
    ;
#elif defined(JC_DOS_CONFORMANCE_V1_1)
  jc_dos_conformance_v1_1();
  for (;;)
    ;
#elif defined(JC_DOS_CONFORMANCE_V1_2)
  jc_dos_conformance_v1_2();
  for (;;)
    ;
#elif defined(JC_DOS_CONFORMANCE_V1_3)
  jc_dos_conformance_v1_3();
  for (;;)
    ;
#elif defined(JC_DOS_CONFORMANCE_V1_4)
  jc_dos_conformance_v1_4();
  for (;;)
    ;
#elif defined(JC_DOS_CONFORMANCE_V1_8)
  jc_dos_conformance_v1_8();
  for (;;)
    ;
#elif defined(JC_DOS_CONFORMANCE_V2_0)
  jc_dos_conformance_v2_0();
  for (;;)
    ;
#else
  err = jc_fs_mount();
  if (err != JC_E_OK) {
    const jc_profile_policy *policy = jc_dos_profile_policy();
    if (err == JC_E_DEV_NOT_FOUND || err == JC_E_DEV_UNSUPPORTED) {
      if (!jc_profile_requires_device(policy, JC_DEVCLASS_STORAGE)) {
        jc_shell_run();
        return 0;
      }
    }
    jc_dos_panic(err);
    return (jc_u8)err;
  }

  jc_shell_run();
  return 0;
#endif
}
