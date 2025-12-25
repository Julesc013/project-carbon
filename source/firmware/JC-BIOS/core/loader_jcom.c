#include "loader_jcom.h"

#include "fs_cpmx.h"
#include "jc_bios.h"
#include "jc_contracts_autogen.h"
#include "jc_util.h"

#define JC_JCOM_IO_BUF 256u

static jc_error_t jc_jcom_read_fully(jc_fs_handle *handle,
                                     jc_u8 *buf,
                                     jc_u32 size) {
  jc_u32 total = 0;
  while (total < size) {
    jc_u32 chunk = 0;
    jc_error_t err =
        jc_fs_read(handle, buf + total, size - total, &chunk);
    if (err != JC_E_OK) {
      return err;
    }
    if (chunk == 0) {
      return JC_E_EXEC_BAD_MAGIC;
    }
    total += chunk;
  }
  return JC_E_OK;
}

jc_error_t jc_jcom_load(const char *name, jc_jcom_image *out_image) {
  jc_fs_handle handle;
  jc_jcom_header_v1 header;
  jc_jcom_header_v1 crc_header;
  jc_u32 file_size;
  jc_u32 expected_size;
  jc_u32 crc;
  jc_u32 remaining;
  jc_u32 offset = 0;
  jc_u8 buffer[JC_JCOM_IO_BUF];
  jc_error_t err;
  jc_u8 *load_ptr;

  if (!name || !out_image) {
    return JC_E_INTERNAL_ASSERT;
  }

  err = jc_fs_open(&handle, name, JC_FS_MODE_READ);
  if (err != JC_E_OK) {
    return err;
  }
  file_size = handle.size_bytes;

  err = jc_jcom_read_fully(&handle, (jc_u8 *)&header, sizeof(header));
  if (err != JC_E_OK) {
    return err;
  }

  if (header.signature != JC_MAGIC_JCOM) {
    return JC_E_EXEC_BAD_MAGIC;
  }
  if (header.header_version != JC_JCOM_HEADER_V1_VERSION) {
    return JC_E_EXEC_BAD_VERSION;
  }
  if (header.header_size != JC_JCOM_HEADER_V1_SIZE) {
    return JC_E_EXEC_BAD_VERSION;
  }
  if (header.reserved0 != 0u || header.reserved1 != 0u) {
    return JC_E_EXEC_BAD_VERSION;
  }
  if (header.load_policy != JC_JCOM_LOAD_FIXED) {
    return JC_E_EXEC_BAD_VERSION;
  }
  if (header.load_addr.hi != 0u) {
    return JC_E_EXEC_BAD_VERSION;
  }
  if (header.entry_offset >= header.image_size) {
    return JC_E_EXEC_BAD_VERSION;
  }
  {
    const jc_capset_v1 *capset = jc_boot_capset();
    if (capset && header.min_cpu_tier > capset->presented_cpu_tier) {
      return JC_E_EXEC_UNSUPPORTED_TIER;
    }
  }

  expected_size = header.header_size + header.image_size + header.tlv_size;
  if (file_size < expected_size) {
    return JC_E_EXEC_BAD_CRC;
  }

  crc = jc_crc32_init();
  jc_memcpy(&crc_header, &header, sizeof(header));
  crc_header.crc32 = 0u;
  crc = jc_crc32_update(crc, (const jc_u8 *)&crc_header, header.header_size);

  load_ptr = (jc_u8 *)(unsigned long)header.load_addr.lo;
  remaining = header.image_size + header.tlv_size;
  while (remaining > 0) {
    jc_u32 chunk = remaining > JC_JCOM_IO_BUF ? JC_JCOM_IO_BUF : remaining;
    jc_u32 got = 0;
    err = jc_fs_read(&handle, buffer, chunk, &got);
    if (err != JC_E_OK) {
      return err;
    }
    if (got == 0) {
      return JC_E_EXEC_BAD_CRC;
    }
    crc = jc_crc32_update(crc, buffer, got);
    if (offset < header.image_size) {
      jc_u32 copy_len = got;
      if (offset + copy_len > header.image_size) {
        copy_len = header.image_size - offset;
      }
      jc_memcpy(load_ptr + offset, buffer, copy_len);
    }
    offset += got;
    remaining -= got;
  }

  crc = jc_crc32_finalize(crc);
  if (crc != header.crc32) {
    return JC_E_EXEC_BAD_CRC;
  }

  jc_memset(load_ptr + header.image_size, 0, header.bss_size);

  out_image->load_addr = header.load_addr.lo;
  out_image->image_size = header.image_size;
  out_image->bss_size = header.bss_size;
  out_image->entry_addr = header.load_addr.lo + header.entry_offset;
  return JC_E_OK;
}

jc_error_t jc_jcom_run(const char *name, jc_u8 *exit_code) {
  jc_jcom_image image;
  jc_error_t err = jc_jcom_load(name, &image);
  jc_u8 rc = 0;
  jc_u8 (*entry)(void);

  if (err != JC_E_OK) {
    return err;
  }

  entry = (jc_u8 (*)(void))(unsigned long)image.entry_addr;
  if (entry) {
    rc = entry();
  }
  if (exit_code) {
    *exit_code = rc;
  }
  return JC_E_OK;
}
