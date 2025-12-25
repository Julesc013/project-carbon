#ifndef JC_DOS_EXEC_JCOM_H
#define JC_DOS_EXEC_JCOM_H

#include "jc_error.h"
#include "jc_types.h"

typedef struct {
  jc_u32 load_addr;
  jc_u32 image_size;
  jc_u32 bss_size;
  jc_u32 entry_addr;
} jc_jcom_image;

jc_error_t jc_exec_jcom_load(const char *name, jc_jcom_image *out_image);
jc_error_t jc_exec_jcom_run(const char *name, jc_u8 *exit_code);
jc_error_t jc_exec_jcom_load_for_tier(const char *name,
                                      jc_u8 effective_tier,
                                      jc_jcom_image *out_image);
jc_error_t jc_exec_jcom_run_for_tier(const char *name,
                                     jc_u8 effective_tier,
                                     jc_u8 *exit_code);

#endif /* JC_DOS_EXEC_JCOM_H */
