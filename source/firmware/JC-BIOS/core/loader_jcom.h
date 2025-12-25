#ifndef JC_LOADER_JCOM_H
#define JC_LOADER_JCOM_H

#include "jc_error.h"
#include "jc_types.h"

typedef struct {
  jc_u32 load_addr;
  jc_u32 image_size;
  jc_u32 bss_size;
  jc_u32 entry_addr;
} jc_jcom_image;

jc_error_t jc_jcom_load(const char *name, jc_jcom_image *out_image);
jc_error_t jc_jcom_run(const char *name, jc_u8 *exit_code);

#endif /* JC_LOADER_JCOM_H */
