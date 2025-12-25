#include "jc_pal.h"

#include "jc_component.h"

static jc_error_t jc_pal_uefi_init(jc_pal_desc *out_desc) {
  (void)out_desc;
  return JC_E_DEV_UNSUPPORTED;
}

void jc_pal_uefi_bind(void) { jc_pal_register(jc_pal_uefi_init); }

static const jc_component_vtable g_pal_uefi_vtable = {0, 0};

const jc_component_desc JC_COMPONENT_DESC = {
    JC_COMPONENT_ID_PAL_UEFI,
    1,
    0,
    1,
    0,
    0,
    &g_pal_uefi_vtable,
    "pal_uefi"};
