#ifndef JC_DOS_FS_ROMFS_H
#define JC_DOS_FS_ROMFS_H

#include "fs_api.h"

jc_error_t jc_romfs_mount(const jc_u8 *image, jc_u32 size_bytes);
jc_error_t jc_romfs_list(jc_fs_list_cb cb, void *ctx);

jc_error_t jc_romfs_open(jc_fs_handle *handle, const char *name, jc_u8 mode);
jc_error_t jc_romfs_read(jc_fs_handle *handle, jc_u8 *buf, jc_u32 len,
                         jc_u32 *out_read);
jc_error_t jc_romfs_close(jc_fs_handle *handle);

#endif /* JC_DOS_FS_ROMFS_H */
