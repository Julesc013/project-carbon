#ifndef JC_FPU_H
#define JC_FPU_H

#include "jc_contracts.h"
#include "jc_error.h"
#include "jc_types.h"

jc_error_t jc_fpu_init(const jc_bdt_header_v1 *bdt,
                       const jc_capset_v1 *capset);
int jc_fpu_has_hw(void);

jc_error_t jc_fpu_f32_add(jc_u32 a, jc_u32 b, jc_u32 *out);
jc_error_t jc_fpu_f32_sub(jc_u32 a, jc_u32 b, jc_u32 *out);
jc_error_t jc_fpu_f32_mul(jc_u32 a, jc_u32 b, jc_u32 *out);

jc_error_t jc_fpu_f32_from_i32(jc_s32 value, jc_u32 *out);
jc_error_t jc_fpu_f32_to_i32(jc_u32 value, jc_s32 *out);

jc_error_t jc_fpu_f32_add_soft(jc_u32 a, jc_u32 b, jc_u32 *out);
jc_error_t jc_fpu_f32_sub_soft(jc_u32 a, jc_u32 b, jc_u32 *out);
jc_error_t jc_fpu_f32_mul_soft(jc_u32 a, jc_u32 b, jc_u32 *out);

#endif /* JC_FPU_H */
