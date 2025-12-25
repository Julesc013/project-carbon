#ifndef JC_FS_CPMX_H
#define JC_FS_CPMX_H

#include "jc_contracts.h"
#include "jc_error.h"
#include "jc_types.h"

#define JC_FS_MODE_READ 0x01u
#define JC_FS_MODE_WRITE 0x02u
#define JC_FS_MODE_CREATE 0x04u
#define JC_FS_MODE_TRUNC 0x08u

typedef struct {
  jc_u8 mode;
  jc_u8 name[8];
  jc_u8 ext[3];
  jc_u32 pos;
  jc_u32 size_bytes;
} jc_fs_handle;

typedef struct {
  jc_u8 name[8];
  jc_u8 ext[3];
  jc_u8 flags;
  jc_u32 size_bytes;
} jc_fs_file_info;

typedef void (*jc_fs_list_cb)(const jc_fs_file_info *info, void *ctx);

jc_error_t jc_fs_mount(void);
jc_error_t jc_fs_list(jc_fs_list_cb cb, void *ctx);

jc_error_t jc_fs_open(jc_fs_handle *handle, const char *name, jc_u8 mode);
jc_error_t jc_fs_read(jc_fs_handle *handle, jc_u8 *buf, jc_u32 len,
                      jc_u32 *out_read);
jc_error_t jc_fs_write(jc_fs_handle *handle, const jc_u8 *buf, jc_u32 len,
                       jc_u32 *out_written);
jc_error_t jc_fs_close(jc_fs_handle *handle);
jc_error_t jc_fs_delete(const char *name);
jc_error_t jc_fs_rename(const char *old_name, const char *new_name);

#endif /* JC_FS_CPMX_H */
