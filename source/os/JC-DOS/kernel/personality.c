#include "personality.h"

#include "exec_jcom.h"
#include "handoff.h"
#include "jc_contracts_autogen.h"

#define JC_PERSONALITY_MAX_SESSIONS 2u
#define JC_PERSONALITY_STACK_MAX 4u

struct jc_personality_session {
  jc_u8 in_use;
  jc_u8 tier;
  jc_u16 flags;
  jc_u32 exec_count;
  jc_error_t last_error;
};

static jc_personality_session g_sessions[JC_PERSONALITY_MAX_SESSIONS];

static jc_u8 g_personality_stack[JC_PERSONALITY_STACK_MAX];
static jc_u8 g_personality_depth;
static jc_u8 g_current_tier;

static int g_force_retmd_fail;

static jc_error_t jc_personality_set_current(jc_u8 tier) {
  if (g_personality_depth >= JC_PERSONALITY_STACK_MAX) {
    return JC_E_MODE_STACK_OVERFLOW;
  }
  g_personality_stack[g_personality_depth++] = g_current_tier;
  g_current_tier = tier;
  return JC_E_OK;
}

static jc_error_t jc_personality_restore_previous(void) {
  if (g_personality_depth == 0u) {
    return JC_E_MODE_STACK_UNDERFLOW;
  }
  g_current_tier = g_personality_stack[--g_personality_depth];
  if (g_force_retmd_fail) {
    return JC_E_MODE_STACK_UNDERFLOW;
  }
  return JC_E_OK;
}

static jc_u8 jc_personality_resolve_tier(jc_u8 tier) {
  const jc_capset_v1 *capset = jc_dos_capset();
  if (tier != JC_PERSONALITY_TIER_NATIVE) {
    return tier;
  }
  if (!capset) {
    return JC_PERSONALITY_TIER_NATIVE;
  }
  return capset->presented_cpu_tier;
}

static int jc_personality_tier_supported(jc_u8 tier) {
  const jc_capset_v1 *capset = jc_dos_capset();
  if (!capset) {
    return 0;
  }
  return tier <= capset->presented_cpu_tier;
}

jc_error_t jc_personality_open(jc_personality_session **out_session,
                               jc_u8 tier,
                               jc_u16 flags) {
  jc_u32 i;
  jc_u8 resolved_tier;
  const jc_capset_v1 *capset = jc_dos_capset();

  if (!out_session) {
    return JC_E_INTERNAL_ASSERT;
  }
  *out_session = 0;
  if (flags != 0u) {
    return JC_E_MODE_NOT_PERMITTED;
  }

  if (g_personality_depth == 0u && g_current_tier == 0u && capset) {
    g_current_tier = capset->presented_cpu_tier;
  }

  resolved_tier = jc_personality_resolve_tier(tier);
  if (resolved_tier == JC_PERSONALITY_TIER_NATIVE) {
    return JC_E_DISCOVERY_BAD_POINTER;
  }
  if (!jc_personality_tier_supported(resolved_tier)) {
    return JC_E_MODE_INVALID_TARGET;
  }

  for (i = 0; i < JC_PERSONALITY_MAX_SESSIONS; ++i) {
    if (!g_sessions[i].in_use) {
      g_sessions[i].in_use = 1;
      g_sessions[i].tier = resolved_tier;
      g_sessions[i].flags = flags;
      g_sessions[i].exec_count = 0;
      g_sessions[i].last_error = JC_E_OK;
      *out_session = &g_sessions[i];
      return JC_E_OK;
    }
  }

  return JC_E_MODE_STACK_OVERFLOW;
}

jc_error_t jc_personality_exec(jc_personality_session *session,
                               const char *jcom_path,
                               jc_u16 exec_flags,
                               jc_u8 *exit_code) {
  jc_error_t err;
  jc_error_t exit_err;

  if (!session || !session->in_use || !jcom_path) {
    return JC_E_INTERNAL_ASSERT;
  }
  if (exec_flags != 0u) {
    return JC_E_MODE_NOT_PERMITTED;
  }

  err = jc_personality_set_current(session->tier);
  if (err != JC_E_OK) {
    session->last_error = err;
    return err;
  }

  err = jc_exec_jcom_run_for_tier(jcom_path, session->tier, exit_code);
  session->exec_count++;

  exit_err = jc_personality_restore_previous();
  if (exit_err != JC_E_OK) {
    session->last_error = exit_err;
    return exit_err;
  }

  session->last_error = err;
  return err;
}

jc_error_t jc_personality_close(jc_personality_session *session) {
  if (!session || !session->in_use) {
    return JC_E_INTERNAL_ASSERT;
  }
  session->in_use = 0;
  session->flags = 0;
  session->tier = 0;
  session->exec_count = 0;
  session->last_error = JC_E_OK;
  return JC_E_OK;
}

void jc_personality_test_force_retmd_fail(int enable) {
  g_force_retmd_fail = enable ? 1 : 0;
}
