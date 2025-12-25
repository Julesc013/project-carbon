#include "video_backends.h"

#include "video_common.h"

jc_error_t jc_video_mda_probe(const jc_bdt_header_v1 *bdt,
                              jc_display_backend *out) {
  const jc_bdt_entry_v1 *entry;
  if (!out) {
    return JC_E_INTERNAL_ASSERT;
  }
  entry = jc_video_find_pio(bdt, JC_DISPLAY_SUBCLASS_MDA);
  if (!entry) {
    return JC_E_DEV_NOT_FOUND;
  }
  (void)entry;
  return JC_E_DEV_UNSUPPORTED;
}
