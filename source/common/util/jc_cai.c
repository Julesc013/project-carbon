#include "jc_cai.h"

#include "jc_config.h"
#include "jc_contracts_autogen.h"

#define JC_CAI_MAX_DEPTH 8u
#define JC_CAI_DEFAULT_DEPTH 4u
#define JC_CAI_COMP_EMPTY 0xFFFFu

typedef struct {
  jc_u16 submit_depth;
  jc_u16 comp_depth;
  jc_u16 submit_head;
  jc_u16 submit_tail;
  jc_u16 comp_head;
  jc_u16 comp_tail;
  jc_u32 mmio_base;
  jc_u16 doorbell_offset;
  jc_u16 reserved0;
} jc_cai_queue;

static jc_cai_queue g_cai;
static int g_cai_ready;
static int g_cai_mock;

static jc_cai_submit_desc_v1 g_submit_ring[JC_CAI_MAX_DEPTH];
static jc_cai_comp_rec_v1 g_comp_ring[JC_CAI_MAX_DEPTH];

static jc_cai_ticks_fn g_ticks_fn;

static jc_cai_mock_handler_fn g_mock_handler;
static void *g_mock_ctx;
static int g_mock_stall;
static int g_mock_bad_tag;

static void jc_cai_fence(void) {
  volatile jc_u32 *p = &g_cai.mmio_base;
  *p = *p;
}

static void *jc_cai_ptr_from_u64(jc_u64 ptr) {
  if (ptr.hi != 0u || ptr.lo == 0u) {
    return 0;
  }
  return (void *)(unsigned long)ptr.lo;
}

static jc_u16 jc_cai_clamp_depth(jc_u32 depth) {
  jc_u16 d = (jc_u16)depth;
  if (d == 0u) {
    d = JC_CAI_DEFAULT_DEPTH;
  }
  if (d > JC_CAI_MAX_DEPTH) {
    d = JC_CAI_MAX_DEPTH;
  }
  if ((d & (d - 1u)) != 0u) {
    jc_u16 p = 1u;
    while ((jc_u16)(p << 1u) <= d) {
      p = (jc_u16)(p << 1u);
    }
    d = p;
  }
  return d;
}

void jc_cai_set_timer(jc_cai_ticks_fn ticks_fn, jc_cai_tick_hz_fn hz_fn) {
  g_ticks_fn = ticks_fn;
  (void)hz_fn;
}

jc_error_t jc_cai_init(const jc_bdt_header_v1 *bdt,
                       const jc_capset_v1 *capset) {
  const jc_bdt_entry_v1 *entry = 0;
  const jc_limits_table_v1 *limits = 0;
  jc_u32 i;

  g_cai_ready = 0;
  g_cai_mock = 0;
  g_cai.submit_head = 0;
  g_cai.submit_tail = 0;
  g_cai.comp_head = 0;
  g_cai.comp_tail = 0;

  if (JC_CFG_ENABLE_CAI == 0) {
    return JC_E_DEV_UNSUPPORTED;
  }
  if (!bdt) {
    return JC_E_DEV_NOT_FOUND;
  }
  if (bdt->signature != JC_MAGIC_BDT ||
      bdt->header_version != JC_BDT_HEADER_V1_VERSION) {
    return JC_E_BDT_BAD_SIGNATURE;
  }

  for (i = 0; i < bdt->entry_count; ++i) {
    const jc_u8 *base = (const jc_u8 *)bdt;
    const jc_u8 *ptr = base + bdt->header_size + i * bdt->entry_size;
    entry = (const jc_bdt_entry_v1 *)ptr;
    if (entry->class_id == JC_DEVCLASS_ACCEL &&
        entry->cai_queue_count != 0u) {
      break;
    }
    entry = 0;
  }

  if (!entry) {
    return JC_E_DEV_NOT_FOUND;
  }

  if (capset) {
    limits = (const jc_limits_table_v1 *)jc_cai_ptr_from_u64(
        capset->limits_table_ptr);
  }
  if (limits) {
    g_cai.submit_depth = jc_cai_clamp_depth(limits->queue_submit_depth);
    g_cai.comp_depth = jc_cai_clamp_depth(limits->queue_complete_depth);
  } else {
    g_cai.submit_depth = JC_CAI_DEFAULT_DEPTH;
    g_cai.comp_depth = JC_CAI_DEFAULT_DEPTH;
  }

  g_cai.mmio_base = entry->mmio_base.lo;
  g_cai.doorbell_offset = entry->cai_doorbell_offset;
  g_cai_mock = (entry->aux_type == JC_CAI_AUX_MOCK);

  for (i = 0; i < JC_CAI_MAX_DEPTH; ++i) {
    g_comp_ring[i].status = JC_CAI_COMP_EMPTY;
    g_comp_ring[i].tag = 0u;
    g_comp_ring[i].ext_status = 0u;
    g_comp_ring[i].bytes_written = 0u;
    g_comp_ring[i].reserved0 = 0u;
  }

  if (!g_cai_mock) {
    return JC_E_DEV_UNSUPPORTED;
  }

  g_cai_ready = 1;
  return JC_E_OK;
}

void jc_cai_reset(void) {
  jc_u32 i;
  g_cai.submit_head = 0;
  g_cai.submit_tail = 0;
  g_cai.comp_head = 0;
  g_cai.comp_tail = 0;
  for (i = 0; i < JC_CAI_MAX_DEPTH; ++i) {
    g_comp_ring[i].status = JC_CAI_COMP_EMPTY;
    g_comp_ring[i].tag = 0u;
  }
}

int jc_cai_is_ready(void) {
  return g_cai_ready != 0;
}

int jc_cai_is_mock(void) {
  return g_cai_mock != 0;
}

jc_u16 jc_cai_submit_depth(void) {
  return g_cai.submit_depth;
}

jc_error_t jc_cai_mock_register(jc_cai_mock_handler_fn handler, void *ctx) {
  g_mock_handler = handler;
  g_mock_ctx = ctx;
  return JC_E_OK;
}

void jc_cai_mock_set_stall(int enable) {
  g_mock_stall = enable ? 1 : 0;
}

void jc_cai_mock_set_bad_tag(int enable) {
  g_mock_bad_tag = enable ? 1 : 0;
}

static jc_error_t jc_cai_ring_doorbell(void) {
  if (g_cai.mmio_base == 0u || g_cai.doorbell_offset == 0u) {
    return JC_E_OK;
  }
  {
    volatile jc_u32 *csr =
        (volatile jc_u32 *)(unsigned long)(g_cai.mmio_base +
                                            g_cai.doorbell_offset);
    *csr = 1u;
  }
  return JC_E_OK;
}

static jc_error_t jc_cai_complete_enqueue(jc_u32 tag,
                                          jc_u16 status,
                                          jc_u32 bytes_written,
                                          jc_u16 ext_status) {
  jc_u16 mask = (jc_u16)(g_cai.comp_depth - 1u);
  jc_u16 idx = g_cai.comp_tail;
  g_comp_ring[idx].tag = tag;
  g_comp_ring[idx].status = status;
  g_comp_ring[idx].ext_status = ext_status;
  g_comp_ring[idx].bytes_written = bytes_written;
  g_comp_ring[idx].reserved0 = 0u;
  g_cai.comp_tail = (jc_u16)((g_cai.comp_tail + 1u) & mask);
  return JC_E_OK;
}

static jc_error_t jc_cai_submit_desc(const jc_cai_submit_desc_v1 *desc) {
  jc_u16 mask = (jc_u16)(g_cai.submit_depth - 1u);
  jc_u16 next = (jc_u16)((g_cai.submit_head + 1u) & mask);
  if (next == g_cai.submit_tail) {
    return JC_E_DEV_IO_TIMEOUT;
  }
  g_submit_ring[g_cai.submit_head] = *desc;
  g_cai.submit_head = next;
  jc_cai_fence();
  jc_cai_ring_doorbell();

  if (g_cai_mock && g_mock_handler && !g_mock_stall) {
    jc_cai_comp_rec_v1 comp;
    jc_error_t err = g_mock_handler(desc, &comp, g_mock_ctx);
    if (err != JC_E_OK) {
      return err;
    }
    if (g_mock_bad_tag) {
      comp.tag ^= 0xFFFFFFFFu;
    }
    jc_cai_complete_enqueue(comp.tag, comp.status, comp.bytes_written,
                            comp.ext_status);
  }
  return JC_E_OK;
}

static jc_u64 jc_cai_deadline(jc_u32 timeout_ticks) {
  jc_u64 now;
  jc_u64 out;
  if (!g_ticks_fn) {
    out.lo = 0;
    out.hi = 0;
    return out;
  }
  now = g_ticks_fn();
  out.lo = now.lo + timeout_ticks;
  out.hi = now.hi + (out.lo < now.lo ? 1u : 0u);
  return out;
}

static int jc_cai_time_expired(jc_u64 deadline) {
  jc_u64 now;
  if (!g_ticks_fn) {
    return 1;
  }
  now = g_ticks_fn();
  if (now.hi > deadline.hi) {
    return 1;
  }
  if (now.hi == deadline.hi && now.lo >= deadline.lo) {
    return 1;
  }
  return 0;
}

static jc_error_t jc_cai_wait_tag(jc_u32 tag,
                                  jc_u32 timeout_ticks,
                                  jc_cai_comp_rec_v1 *out_comp) {
  jc_u16 mask = (jc_u16)(g_cai.comp_depth - 1u);
  jc_u64 deadline = jc_cai_deadline(timeout_ticks);

  for (;;) {
    jc_cai_comp_rec_v1 *comp = &g_comp_ring[g_cai.comp_head];
    if (comp->status != JC_CAI_COMP_EMPTY) {
      jc_u16 status = comp->status;
      jc_u32 comp_tag = comp->tag;
      if (out_comp) {
        *out_comp = *comp;
      }
      comp->status = JC_CAI_COMP_EMPTY;
      g_cai.comp_head = (jc_u16)((g_cai.comp_head + 1u) & mask);
      g_cai.submit_tail = (jc_u16)((g_cai.submit_tail + 1u) &
                                   (g_cai.submit_depth - 1u));
      if (comp_tag != tag) {
        return JC_E_DEV_IO_ERROR;
      }
      if (status != JC_CAI_STATUS_OK) {
        return JC_E_DEV_IO_ERROR;
      }
      return JC_E_OK;
    }
    if (timeout_ticks == 0u || jc_cai_time_expired(deadline)) {
      return JC_E_DEV_IO_TIMEOUT;
    }
  }
}

jc_error_t jc_cai_submit_nowait(const jc_cai_submit_desc_v1 *desc) {
  if (!g_cai_ready) {
    return JC_E_DEV_UNSUPPORTED;
  }
  if (!desc) {
    return JC_E_INTERNAL_ASSERT;
  }
  return jc_cai_submit_desc(desc);
}

jc_error_t jc_cai_submit(const jc_cai_submit_desc_v1 *desc,
                         jc_u32 timeout_ticks,
                         jc_cai_comp_rec_v1 *out_comp) {
  jc_error_t err;
  if (!g_cai_ready) {
    return JC_E_DEV_UNSUPPORTED;
  }
  if (!g_ticks_fn) {
    return JC_E_DEV_UNSUPPORTED;
  }
  if (!desc) {
    return JC_E_INTERNAL_ASSERT;
  }
  err = jc_cai_submit_desc(desc);
  if (err != JC_E_OK) {
    return err;
  }
  return jc_cai_wait_tag(desc->tag, timeout_ticks, out_comp);
}
