#include "jc_mode.h"

#include "jc_contracts_autogen.h"
#include "jc_offsets_autogen.h"
#include "jc_util.h"

#define JC_MODE_STACK_MAX 16u

static jc_u8 g_mode_current = 0;
static jc_u8 g_mode_max = 0;
static jc_u8 g_mode_stack[JC_MODE_STACK_MAX];
static jc_u8 g_mode_depth = 0;
static jc_error_t g_mode_last_error = JC_E_OK;

volatile jc_mode_abi_v1 *jc_mode_capsule_ptr = 0;

void jc_modeup_tramp(void);
void jc_retmd_tramp(void);

static jc_error_t jc_mode_validate_capsule(jc_mode_abi_v1 *capsule) {
  if (!capsule) {
    return JC_E_INTERNAL_ASSERT;
  }
  if (capsule->version != JC_MODE_ABI_V1_VERSION) {
    capsule->error_code = JC_MODE_TRAP_INVALID_TARGET;
    return JC_E_MODE_INVALID_TARGET;
  }
  if (capsule->size_bytes != JC_STRUCT_MODE_ABI_V1_SIZE) {
    capsule->error_code = JC_MODE_TRAP_INVALID_TARGET;
    return JC_E_MODE_INVALID_TARGET;
  }
  if (capsule->reserved0 != 0 || capsule->reserved1 != 0) {
    capsule->error_code = JC_MODE_TRAP_FRAME_CORRUPT;
    return JC_E_MODE_NOT_PERMITTED;
  }
  return JC_E_OK;
}

void jc_modeup_emulate(void) {
  jc_mode_abi_v1 *capsule = (jc_mode_abi_v1 *)jc_mode_capsule_ptr;
  void (*entry)(void);
  if (!capsule) {
    g_mode_last_error = JC_E_INTERNAL_ASSERT;
    return;
  }
  capsule->error_code = 0;
  if (capsule->target_tier <= g_mode_current || capsule->target_tier > g_mode_max) {
    capsule->error_code = JC_MODE_TRAP_INVALID_TARGET;
    g_mode_last_error = JC_E_MODE_INVALID_TARGET;
    return;
  }
  if (capsule->entry_vector.hi != 0u) {
    capsule->error_code = JC_MODE_TRAP_INVALID_ENTRY;
    g_mode_last_error = JC_E_MODE_NOT_PERMITTED;
    return;
  }
  if (capsule->entry_vector.lo == 0u) {
    capsule->error_code = JC_MODE_TRAP_INVALID_ENTRY;
    g_mode_last_error = JC_E_MODE_NOT_PERMITTED;
    return;
  }
  if (g_mode_depth >= JC_MODE_STACK_MAX) {
    capsule->error_code = JC_MODE_TRAP_STACK_OVERFLOW;
    g_mode_last_error = JC_E_MODE_STACK_OVERFLOW;
    return;
  }
  g_mode_stack[g_mode_depth++] = g_mode_current;
  g_mode_current = capsule->target_tier;

  entry = (void (*)(void))(unsigned long)capsule->entry_vector.lo;
  if (entry) {
    entry();
  }
  capsule->return_pc = jc_u64_make(0, 0);
  g_mode_last_error = JC_E_OK;
}

void jc_retmd_emulate(void) {
  if (g_mode_depth == 0) {
    g_mode_last_error = JC_E_MODE_STACK_UNDERFLOW;
    return;
  }
  g_mode_current = g_mode_stack[--g_mode_depth];
  g_mode_last_error = JC_E_OK;
}

jc_error_t jc_mode_init(jc_u8 current_tier, jc_u8 max_tier) {
  g_mode_current = current_tier;
  g_mode_max = max_tier;
  g_mode_depth = 0;
  return JC_E_OK;
}

jc_u8 jc_mode_current_tier(void) {
  return g_mode_current;
}

jc_error_t jc_modeup_request(jc_mode_abi_v1 *capsule) {
  jc_error_t err = jc_mode_validate_capsule(capsule);
  if (err != JC_E_OK) {
    g_mode_last_error = err;
    return err;
  }
  jc_mode_capsule_ptr = capsule;
  g_mode_last_error = JC_E_INTERNAL_ASSERT;
  jc_modeup_tramp();
  return g_mode_last_error;
}

jc_error_t jc_retmd_request(void) {
  g_mode_last_error = JC_E_INTERNAL_ASSERT;
  jc_retmd_tramp();
  return g_mode_last_error;
}

jc_error_t jc_mode_self_test(void) {
  return JC_E_OK;
}
