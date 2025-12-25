#include "jc_pal.h"

#include "jc_contracts_autogen.h"

static jc_pal_init_fn g_pal_init = 0;

static void jc_pal_zero(void *ptr, jc_u32 len) {
  jc_u8 *out = (jc_u8 *)ptr;
  while (len--) {
    *out++ = 0;
  }
}

static int jc_pal_str_valid(const char *s) {
  if (!s || !*s) {
    return 0;
  }
  return 1;
}

static int jc_pal_console_valid(const jc_pal_console *console) {
  return console && console->vtable && console->vtable->write;
}

static int jc_pal_block_valid(const jc_pal_block *block) {
  return block && block->vtable && block->vtable->read &&
         block->vtable->get_params;
}

static int jc_pal_timer_valid(const jc_pal_timer *timer) {
  return timer && timer->vtable && timer->vtable->ticks &&
         timer->vtable->tick_hz;
}

static int jc_pal_memmap_valid(const jc_pal_memmap *memmap) {
  return memmap && memmap->vtable && memmap->vtable->get_table;
}

static jc_error_t jc_pal_validate_bdt(const jc_bdt_header_v1 *bdt) {
  if (!bdt) {
    return JC_E_BDT_BAD_SIZE;
  }
  if (bdt->signature != JC_MAGIC_BDT) {
    return JC_E_BDT_BAD_SIGNATURE;
  }
  if (bdt->header_version != JC_BDT_HEADER_V1_VERSION) {
    return JC_E_BDT_BAD_VERSION;
  }
  if (bdt->header_size != JC_BDT_HEADER_V1_SIZE) {
    return JC_E_BDT_BAD_SIZE;
  }
  if (bdt->entry_size != JC_BDT_ENTRY_V1_SIZE) {
    return JC_E_BDT_BAD_SIZE;
  }
  return JC_E_OK;
}

static jc_error_t jc_pal_validate_capset(const jc_capset_v1 *capset) {
  if (!capset) {
    return JC_E_DISCOVERY_BAD_SIZE;
  }
  if (capset->signature != JC_MAGIC_CAPSET) {
    return JC_E_DISCOVERY_BAD_SIGNATURE;
  }
  if (capset->version != JC_CAPSET_V1_VERSION) {
    return JC_E_DISCOVERY_BAD_VERSION;
  }
  if (capset->size_bytes != JC_CAPSET_V1_SIZE) {
    return JC_E_DISCOVERY_BAD_SIZE;
  }
  return JC_E_OK;
}

void jc_pal_register(jc_pal_init_fn init_fn) { g_pal_init = init_fn; }

jc_error_t jc_pal_init(jc_pal_desc *out_desc) {
  jc_error_t err;
  if (!out_desc) {
    return JC_E_INTERNAL_ASSERT;
  }
  jc_pal_zero(out_desc, sizeof(*out_desc));
  out_desc->abi_major = JC_PAL_ABI_MAJOR;
  out_desc->abi_minor = JC_PAL_ABI_MINOR;
  if (!g_pal_init) {
    return JC_E_DEV_UNSUPPORTED;
  }
  err = g_pal_init(out_desc);
  if (err != JC_E_OK) {
    return err;
  }
  return jc_pal_validate(out_desc);
}

jc_error_t jc_pal_validate(const jc_pal_desc *desc) {
  jc_error_t err;
  const jc_mem_region_header_v1 *mem_table;
  if (!desc) {
    return JC_E_INTERNAL_ASSERT;
  }
  if (desc->abi_major != JC_PAL_ABI_MAJOR ||
      desc->abi_minor > JC_PAL_ABI_MINOR) {
    return JC_E_DEV_UNSUPPORTED;
  }
  if (!jc_pal_str_valid(desc->platform_id) ||
      !jc_pal_str_valid(desc->platform_version)) {
    return JC_E_DEV_UNSUPPORTED;
  }
  if (!jc_pal_console_valid(&desc->console) ||
      !jc_pal_block_valid(&desc->block) || !jc_pal_timer_valid(&desc->timer) ||
      !jc_pal_memmap_valid(&desc->memmap)) {
    return JC_E_DEV_UNSUPPORTED;
  }
  err = jc_pal_validate_bdt(desc->bdt);
  if (err != JC_E_OK) {
    return err;
  }
  err = jc_pal_validate_capset(desc->capset);
  if (err != JC_E_OK) {
    return err;
  }
  if ((desc->platform_caps & JC_CAP_HAS_V86) != 0u &&
      !JC_CAP_CHECK(desc->capset, JC_CAP_HAS_V86)) {
    return JC_E_DEV_UNSUPPORTED;
  }
  if ((desc->platform_caps & JC_CAP_HAS_ROMWBW) != 0u &&
      !JC_CAP_CHECK(desc->capset, JC_CAP_HAS_ROMWBW)) {
    return JC_E_DEV_UNSUPPORTED;
  }
  if ((desc->platform_caps & JC_CAP_HAS_LOCAL_VIDEO) != 0u &&
      !JC_CAP_CHECK(desc->capset, JC_CAP_HAS_LOCAL_VIDEO)) {
    return JC_E_DEV_UNSUPPORTED;
  }
  if ((desc->platform_caps & JC_CAP_HAS_PAGING) != 0u &&
      !JC_CAP_CHECK(desc->capset, JC_CAP_HAS_PAGING)) {
    return JC_E_DEV_UNSUPPORTED;
  }
  if ((desc->platform_caps & JC_CAP_HAS_IRQ) != 0u &&
      !JC_CAP_CHECK(desc->capset, JC_CAP_HAS_IRQ)) {
    return JC_E_DEV_UNSUPPORTED;
  }
  mem_table = desc->memmap.vtable->get_table(desc->memmap.ctx);
  if (!mem_table) {
    return JC_E_DISCOVERY_BAD_SIZE;
  }
  if (mem_table->signature != JC_MAGIC_MEM_REGION_HEADER) {
    return JC_E_DISCOVERY_BAD_SIGNATURE;
  }
  return JC_E_OK;
}
