#include "pcbios_boot.h"

#include "jc_util.h"

jc_error_t jc_pcbios_stage2_prepare(jc_dos_handoff_v1 *handoff,
                                    const jc_pal_desc *pal,
                                    jc_u32 tpa_base,
                                    jc_u32 tpa_size,
                                    jc_u64 services_ptr) {
  if (!handoff || !pal || !pal->capset || !pal->bdt) {
    return JC_E_INTERNAL_ASSERT;
  }
  jc_memset(handoff, 0, sizeof(*handoff));
  handoff->signature = JC_DOS_HANDOFF_V1_SIGNATURE;
  handoff->version = JC_DOS_HANDOFF_V1_VERSION;
  handoff->size_bytes = (jc_u16)sizeof(*handoff);
  handoff->tpa_base = tpa_base;
  handoff->tpa_size = tpa_size;
  handoff->capset_ptr = jc_u64_make((jc_u32)(unsigned long)pal->capset, 0);
  handoff->bdt_ptr = jc_u64_make((jc_u32)(unsigned long)pal->bdt, 0);
  handoff->services_ptr = services_ptr;
  return JC_E_OK;
}

jc_error_t jc_pcbios_stage2_handoff(const jc_pcbios_boot_ops *ops,
                                    jc_pcbios_kernel_entry_fn entry,
                                    jc_u32 tpa_base,
                                    jc_u32 tpa_size,
                                    jc_u64 services_ptr) {
  jc_pal_desc pal;
  jc_dos_handoff_v1 handoff;
  jc_error_t err;

  err = jc_pal_init(&pal);
  if (err != JC_E_OK) {
    if (ops && ops->console_write) {
      ops->console_write(ops->ctx, "PAL init failed\n", 16);
    }
    return err;
  }
  err = jc_pcbios_stage2_prepare(&handoff, &pal, tpa_base, tpa_size,
                                 services_ptr);
  if (err != JC_E_OK) {
    return err;
  }
  if (entry) {
    entry(&handoff);
  }
  return JC_E_OK;
}
