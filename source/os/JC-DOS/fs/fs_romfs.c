#include "fs_romfs.h"

jc_error_t jc_romfs_mount(const jc_u8 *image, jc_u32 size_bytes) {
  (void)image;
  (void)size_bytes;
  return JC_E_DEV_UNSUPPORTED;
}

jc_error_t jc_romfs_list(jc_fs_list_cb cb, void *ctx) {
  (void)cb;
  (void)ctx;
  return JC_E_DEV_UNSUPPORTED;
}

jc_error_t jc_romfs_open(jc_fs_handle *handle, const char *name, jc_u8 mode) {
  (void)handle;
  (void)name;
  (void)mode;
  return JC_E_DEV_UNSUPPORTED;
}

jc_error_t jc_romfs_read(jc_fs_handle *handle, jc_u8 *buf, jc_u32 len,
                         jc_u32 *out_read) {
  (void)handle;
  (void)buf;
  (void)len;
  if (out_read) {
    *out_read = 0;
  }
  return JC_E_DEV_UNSUPPORTED;
}

jc_error_t jc_romfs_close(jc_fs_handle *handle) {
  (void)handle;
  return JC_E_DEV_UNSUPPORTED;
}
