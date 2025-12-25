#include "jc_fpu.h"

#include "jc_cai.h"
#include "jc_config.h"
#include "jc_contracts_autogen.h"

int jc_fpu_cai_init(void);
jc_error_t jc_fpu_f32_add_cai(jc_u32 a, jc_u32 b, jc_u32 *out);
jc_error_t jc_fpu_f32_sub_cai(jc_u32 a, jc_u32 b, jc_u32 *out);
jc_error_t jc_fpu_f32_mul_cai(jc_u32 a, jc_u32 b, jc_u32 *out);

int jc_fpu_am9511_init(const jc_bdt_header_v1 *bdt);
int jc_fpu_am9512_init(const jc_bdt_header_v1 *bdt);

static int g_fpu_has_hw;

static jc_error_t (*g_fpu_add)(jc_u32, jc_u32, jc_u32 *) = jc_fpu_f32_add_soft;
static jc_error_t (*g_fpu_sub)(jc_u32, jc_u32, jc_u32 *) = jc_fpu_f32_sub_soft;
static jc_error_t (*g_fpu_mul)(jc_u32, jc_u32, jc_u32 *) = jc_fpu_f32_mul_soft;

jc_error_t jc_fpu_init(const jc_bdt_header_v1 *bdt,
                       const jc_capset_v1 *capset) {
  jc_u32 fpu_word0 = 0u;

  g_fpu_has_hw = 0;
  g_fpu_add = jc_fpu_f32_add_soft;
  g_fpu_sub = jc_fpu_f32_sub_soft;
  g_fpu_mul = jc_fpu_f32_mul_soft;

  if (JC_CFG_ENABLE_FPU == 0) {
    return JC_E_OK;
  }
  if (capset) {
    fpu_word0 = capset->fpu_features[0];
  }

  if ((fpu_word0 & JC_FPU_FEAT_AM9513_ASYNC_SCALAR_MASK) != 0u &&
      jc_cai_is_ready() && jc_fpu_cai_init()) {
    g_fpu_has_hw = 1;
    g_fpu_add = jc_fpu_f32_add_cai;
    g_fpu_sub = jc_fpu_f32_sub_cai;
    g_fpu_mul = jc_fpu_f32_mul_cai;
    return JC_E_OK;
  }

  if ((fpu_word0 & JC_FPU_FEAT_AM9512_IEEE_PLUS_MASK) != 0u) {
    if (jc_fpu_am9512_init(bdt)) {
      g_fpu_has_hw = 1;
      return JC_E_OK;
    }
  }

  if (jc_fpu_am9511_init(bdt)) {
    g_fpu_has_hw = 1;
  }
  return JC_E_OK;
}

int jc_fpu_has_hw(void) {
  return g_fpu_has_hw;
}

jc_error_t jc_fpu_f32_add(jc_u32 a, jc_u32 b, jc_u32 *out) {
  return g_fpu_add(a, b, out);
}

jc_error_t jc_fpu_f32_sub(jc_u32 a, jc_u32 b, jc_u32 *out) {
  return g_fpu_sub(a, b, out);
}

jc_error_t jc_fpu_f32_mul(jc_u32 a, jc_u32 b, jc_u32 *out) {
  return g_fpu_mul(a, b, out);
}
