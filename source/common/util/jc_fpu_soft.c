#include "jc_fpu.h"

#define JC_FPU_F32_SIGN_MASK 0x80000000u
#define JC_FPU_F32_EXP_MASK 0x7F800000u
#define JC_FPU_F32_FRAC_MASK 0x007FFFFFu
#define JC_FPU_F32_EXP_BIAS 127
#define JC_FPU_F32_MAX_EXACT_INT 0x00FFFFFFu

jc_error_t jc_fpu_f32_from_i32(jc_s32 value, jc_u32 *out) {
  jc_u32 sign = 0u;
  jc_u32 abs;
  jc_u32 msb = 0;
  jc_u32 exp;
  jc_u32 frac;

  if (!out) {
    return JC_E_INTERNAL_ASSERT;
  }
  if (value == 0) {
    *out = 0u;
    return JC_E_OK;
  }
  if (value < 0) {
    sign = JC_FPU_F32_SIGN_MASK;
    abs = (jc_u32)(-value);
  } else {
    abs = (jc_u32)value;
  }
  if (abs > JC_FPU_F32_MAX_EXACT_INT) {
    return JC_E_DEV_UNSUPPORTED;
  }
  for (msb = 0; msb < 31; ++msb) {
    if (abs & (1u << (31u - msb))) {
      msb = 31u - msb;
      break;
    }
  }
  exp = (jc_u32)(msb + JC_FPU_F32_EXP_BIAS);
  frac = (abs << (23u - msb)) & JC_FPU_F32_FRAC_MASK;
  *out = sign | (exp << 23) | frac;
  return JC_E_OK;
}

jc_error_t jc_fpu_f32_to_i32(jc_u32 value, jc_s32 *out) {
  jc_u32 sign = value & JC_FPU_F32_SIGN_MASK;
  jc_u32 exp = (value & JC_FPU_F32_EXP_MASK) >> 23;
  jc_u32 frac = value & JC_FPU_F32_FRAC_MASK;
  jc_u32 mant;
  jc_s32 result;
  int shift;

  if (!out) {
    return JC_E_INTERNAL_ASSERT;
  }
  if (exp == 0 && frac == 0u) {
    *out = 0;
    return JC_E_OK;
  }
  if (exp == 0 || exp == 0xFFu) {
    return JC_E_DEV_UNSUPPORTED;
  }
  shift = (int)exp - JC_FPU_F32_EXP_BIAS;
  mant = (1u << 23) | frac;
  if (shift < 0) {
    return JC_E_DEV_UNSUPPORTED;
  }
  if (shift > 30) {
    return JC_E_DEV_UNSUPPORTED;
  }
  if (shift > 23) {
    mant = mant << (shift - 23);
  } else {
    jc_u32 mask = (1u << (23 - shift)) - 1u;
    if ((mant & mask) != 0u) {
      return JC_E_DEV_UNSUPPORTED;
    }
    mant = mant >> (23 - shift);
  }
  result = (jc_s32)mant;
  if (sign) {
    result = -result;
  }
  *out = result;
  return JC_E_OK;
}

jc_error_t jc_fpu_f32_add_soft(jc_u32 a, jc_u32 b, jc_u32 *out) {
  jc_s32 ia;
  jc_s32 ib;
  jc_s32 sum;
  jc_error_t err;

  if (!out) {
    return JC_E_INTERNAL_ASSERT;
  }
  err = jc_fpu_f32_to_i32(a, &ia);
  if (err != JC_E_OK) {
    return err;
  }
  err = jc_fpu_f32_to_i32(b, &ib);
  if (err != JC_E_OK) {
    return err;
  }
  sum = ia + ib;
  if (sum > (jc_s32)JC_FPU_F32_MAX_EXACT_INT ||
      sum < -(jc_s32)JC_FPU_F32_MAX_EXACT_INT) {
    return JC_E_DEV_UNSUPPORTED;
  }
  return jc_fpu_f32_from_i32(sum, out);
}

jc_error_t jc_fpu_f32_sub_soft(jc_u32 a, jc_u32 b, jc_u32 *out) {
  jc_s32 ia;
  jc_s32 ib;
  jc_s32 diff;
  jc_error_t err;

  if (!out) {
    return JC_E_INTERNAL_ASSERT;
  }
  err = jc_fpu_f32_to_i32(a, &ia);
  if (err != JC_E_OK) {
    return err;
  }
  err = jc_fpu_f32_to_i32(b, &ib);
  if (err != JC_E_OK) {
    return err;
  }
  diff = ia - ib;
  if (diff > (jc_s32)JC_FPU_F32_MAX_EXACT_INT ||
      diff < -(jc_s32)JC_FPU_F32_MAX_EXACT_INT) {
    return JC_E_DEV_UNSUPPORTED;
  }
  return jc_fpu_f32_from_i32(diff, out);
}

jc_error_t jc_fpu_f32_mul_soft(jc_u32 a, jc_u32 b, jc_u32 *out) {
  jc_s32 ia;
  jc_s32 ib;
  jc_s32 prod;
  jc_error_t err;

  if (!out) {
    return JC_E_INTERNAL_ASSERT;
  }
  err = jc_fpu_f32_to_i32(a, &ia);
  if (err != JC_E_OK) {
    return err;
  }
  err = jc_fpu_f32_to_i32(b, &ib);
  if (err != JC_E_OK) {
    return err;
  }
  if (ia > 0x0000FFFF || ia < -0x0000FFFF ||
      ib > 0x0000FFFF || ib < -0x0000FFFF) {
    return JC_E_DEV_UNSUPPORTED;
  }
  prod = ia * ib;
  if (prod > (jc_s32)JC_FPU_F32_MAX_EXACT_INT ||
      prod < -(jc_s32)JC_FPU_F32_MAX_EXACT_INT) {
    return JC_E_DEV_UNSUPPORTED;
  }
  return jc_fpu_f32_from_i32(prod, out);
}
