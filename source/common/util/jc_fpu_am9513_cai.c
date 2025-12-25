#include "jc_fpu.h"

#include "jc_cai.h"
#include "jc_contracts_autogen.h"

#define JC_AM95_OP_F32_ADD 0x0001u
#define JC_AM95_OP_F32_SUB 0x0002u
#define JC_AM95_OP_F32_MUL 0x0003u

#define JC_FPU_CAI_TIMEOUT_TICKS 50000u

static jc_u32 g_fpu_cai_tag = 1u;
static int g_fpu_cai_ready;

static void jc_fpu_memset(void *dst, jc_u8 value, jc_u32 len) {
  jc_u32 i;
  jc_u8 *d = (jc_u8 *)dst;
  if (!d) {
    return;
  }
  for (i = 0; i < len; ++i) {
    d[i] = value;
  }
}

static void *jc_fpu_ptr_from_u64(jc_u64 ptr) {
  if (ptr.hi != 0u || ptr.lo == 0u) {
    return 0;
  }
  return (void *)(unsigned long)ptr.lo;
}

static jc_error_t jc_fpu_cai_mock_handler(const jc_cai_submit_desc_v1 *desc,
                                          jc_cai_comp_rec_v1 *comp,
                                          void *ctx) {
  jc_cai_operand_desc_v1 *ops;
  jc_u32 *result_ptr;
  jc_error_t err = JC_E_OK;
  jc_u32 out = 0;

  (void)ctx;
  if (!desc || !comp) {
    return JC_E_INTERNAL_ASSERT;
  }
  if (desc->desc_version != JC_CAI_SUBMIT_DESC_V1_VERSION ||
      desc->desc_size_dw != (JC_CAI_SUBMIT_DESC_V1_SIZE / 4u)) {
    comp->tag = desc->tag;
    comp->status = JC_CAI_STATUS_INVALID_OP;
    comp->ext_status = 0;
    comp->bytes_written = 0;
    comp->reserved0 = 0;
    return JC_E_OK;
  }
  if (desc->opcode_group != JC_CAI_OPCODE_GROUP_AM95_SCALAR ||
      desc->operand_count != 2u || desc->result_len < 4u) {
    comp->tag = desc->tag;
    comp->status = JC_CAI_STATUS_INVALID_OP;
    comp->ext_status = 0;
    comp->bytes_written = 0;
    comp->reserved0 = 0;
    return JC_E_OK;
  }

  ops = (jc_cai_operand_desc_v1 *)jc_fpu_ptr_from_u64(desc->operands_ptr);
  result_ptr = (jc_u32 *)jc_fpu_ptr_from_u64(desc->result_ptr);
  if (!ops || !result_ptr) {
    comp->tag = desc->tag;
    comp->status = JC_CAI_STATUS_FAULT;
    comp->ext_status = 0;
    comp->bytes_written = 0;
    comp->reserved0 = 0;
    return JC_E_OK;
  }

  {
    jc_u32 *op0_ptr = (jc_u32 *)jc_fpu_ptr_from_u64(ops[0].ptr);
    jc_u32 *op1_ptr = (jc_u32 *)jc_fpu_ptr_from_u64(ops[1].ptr);
    if (!op0_ptr || !op1_ptr) {
      comp->tag = desc->tag;
      comp->status = JC_CAI_STATUS_FAULT;
      comp->ext_status = 0;
      comp->bytes_written = 0;
      comp->reserved0 = 0;
      return JC_E_OK;
    }

    switch (desc->opcode) {
      case JC_AM95_OP_F32_ADD:
        err = jc_fpu_f32_add_soft(*op0_ptr, *op1_ptr, &out);
        break;
      case JC_AM95_OP_F32_SUB:
        err = jc_fpu_f32_sub_soft(*op0_ptr, *op1_ptr, &out);
        break;
      case JC_AM95_OP_F32_MUL:
        err = jc_fpu_f32_mul_soft(*op0_ptr, *op1_ptr, &out);
        break;
      default:
        err = JC_E_DEV_UNSUPPORTED;
        break;
    }
  }

  if (err != JC_E_OK) {
    comp->tag = desc->tag;
    comp->status = JC_CAI_STATUS_UNSUPPORTED;
    comp->ext_status = 0;
    comp->bytes_written = 0;
    comp->reserved0 = 0;
    return JC_E_OK;
  }

  *result_ptr = out;
  comp->tag = desc->tag;
  comp->status = JC_CAI_STATUS_OK;
  comp->ext_status = 0;
  comp->bytes_written = 4u;
  comp->reserved0 = 0;
  return JC_E_OK;
}

static jc_error_t jc_fpu_cai_submit_bin(jc_u32 opcode,
                                        jc_u32 a,
                                        jc_u32 b,
                                        jc_u32 *out) {
  jc_cai_operand_desc_v1 ops[2];
  jc_cai_submit_desc_v1 desc;
  jc_cai_comp_rec_v1 comp;
  jc_u32 result = 0;
  jc_error_t err;

  if (!out) {
    return JC_E_INTERNAL_ASSERT;
  }
  if (!g_fpu_cai_ready) {
    return JC_E_DEV_UNSUPPORTED;
  }

  jc_fpu_memset(&desc, 0, sizeof(desc));
  jc_fpu_memset(&comp, 0, sizeof(comp));
  jc_fpu_memset(&ops, 0, sizeof(ops));

  ops[0].ptr.lo = (jc_u32)(unsigned long)&a;
  ops[0].ptr.hi = 0;
  ops[0].len = 4u;
  ops[0].stride = 0u;
  ops[0].flags = 0u;
  ops[0].reserved0 = 0u;
  ops[0].reserved1.lo = 0u;
  ops[0].reserved1.hi = 0u;

  ops[1].ptr.lo = (jc_u32)(unsigned long)&b;
  ops[1].ptr.hi = 0;
  ops[1].len = 4u;
  ops[1].stride = 0u;
  ops[1].flags = 0u;
  ops[1].reserved0 = 0u;
  ops[1].reserved1.lo = 0u;
  ops[1].reserved1.hi = 0u;

  desc.desc_version = JC_CAI_SUBMIT_DESC_V1_VERSION;
  desc.desc_size_dw = (jc_u16)(JC_CAI_SUBMIT_DESC_V1_SIZE / 4u);
  desc.opcode = opcode;
  desc.flags = 0u;
  desc.context_id = 0xFFFFu;
  desc.operand_count = 2u;
  desc.tag = g_fpu_cai_tag++;
  desc.opcode_group = JC_CAI_OPCODE_GROUP_AM95_SCALAR;
  desc.format_primary = 0u;
  desc.format_aux = 0u;
  desc.format_flags = 0u;
  desc.operands_ptr.lo = (jc_u32)(unsigned long)&ops[0];
  desc.operands_ptr.hi = 0u;
  desc.result_ptr.lo = (jc_u32)(unsigned long)&result;
  desc.result_ptr.hi = 0u;
  desc.result_len = 4u;
  desc.result_stride = 0u;
  desc.tensor_desc_ptr.lo = 0u;
  desc.tensor_desc_ptr.hi = 0u;
  desc.tensor_desc_len = 0u;
  desc.tensor_rank = 0u;
  desc.tensor_desc_flags = 0u;
  desc.reserved2 = 0u;

  err = jc_cai_submit(&desc, JC_FPU_CAI_TIMEOUT_TICKS, &comp);
  if (err != JC_E_OK) {
    return err;
  }
  if (comp.status != JC_CAI_STATUS_OK) {
    return JC_E_DEV_IO_ERROR;
  }
  *out = result;
  return JC_E_OK;
}

int jc_fpu_cai_init(void) {
  if (!jc_cai_is_ready() || !jc_cai_is_mock()) {
    g_fpu_cai_ready = 0;
    return 0;
  }
  g_fpu_cai_ready = 1;
  jc_cai_mock_register(jc_fpu_cai_mock_handler, 0);
  return 1;
}

jc_error_t jc_fpu_f32_add_cai(jc_u32 a, jc_u32 b, jc_u32 *out) {
  return jc_fpu_cai_submit_bin(JC_AM95_OP_F32_ADD, a, b, out);
}

jc_error_t jc_fpu_f32_sub_cai(jc_u32 a, jc_u32 b, jc_u32 *out) {
  return jc_fpu_cai_submit_bin(JC_AM95_OP_F32_SUB, a, b, out);
}

jc_error_t jc_fpu_f32_mul_cai(jc_u32 a, jc_u32 b, jc_u32 *out) {
  return jc_fpu_cai_submit_bin(JC_AM95_OP_F32_MUL, a, b, out);
}
