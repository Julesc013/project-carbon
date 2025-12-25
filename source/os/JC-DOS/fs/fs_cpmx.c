#include "fs_api.h"

#include "bios_services.h"
#include "cache_blk.h"
#include "jc_contracts.h"
#include "jc_contracts_autogen.h"
#include "jc_dos_util.h"
#include "mem_arena.h"

typedef struct {
  int mounted;
  jc_cpmx_superblock_v1 super;
  jc_u32 sector_size;
  jc_u32 sector_units;
  jc_u32 sectors_per_block;
  jc_u32 sectors_per_block_512;
  jc_u32 block_size;
  jc_u8 *block_buf;
  jc_u32 dir_bytes;
  jc_u32 dir_region_bytes;
  jc_u32 dir_lba_512;
  jc_u32 dir_sectors_512;
  jc_u32 data_lba_512;
  jc_u32 alloc_block_count;
  jc_cpmx_dir_entry_v1 *dir_entries;
  jc_u8 *alloc_map;
  jc_u32 alloc_map_bytes;
  int dir_dirty;
} jc_fs_context;

static jc_fs_context g_fs;
static jc_u8 g_fs_sector_buf[512];

static int jc_fs_is_valid_char(jc_u8 c) {
  if (c >= 'A' && c <= 'Z') {
    return 1;
  }
  if (c >= '0' && c <= '9') {
    return 1;
  }
  if (c == '_' || c == '-') {
    return 1;
  }
  return 0;
}

static jc_u8 jc_fs_to_upper(jc_u8 c) {
  if (c >= 'a' && c <= 'z') {
    return (jc_u8)(c - 'a' + 'A');
  }
  return c;
}

static int jc_fs_parse_name(const char *name_in,
                            jc_u8 name_out[8],
                            jc_u8 ext_out[3]) {
  jc_u32 i = 0;
  jc_u32 name_len = 0;
  jc_u32 ext_len = 0;
  int seen_dot = 0;

  if (!name_in) {
    return 0;
  }
  while (name_in[i] != '\0' && jc_dos_is_space(name_in[i])) {
    i++;
  }
  if (name_in[i] == '\0') {
    return 0;
  }

  for (name_len = 0; name_len < 8; ++name_len) {
    char c = name_in[i];
    if (c == '\0' || c == '.' || jc_dos_is_space(c)) {
      break;
    }
    c = (char)jc_fs_to_upper((jc_u8)c);
    if (!jc_fs_is_valid_char((jc_u8)c)) {
      return 0;
    }
    name_out[name_len] = (jc_u8)c;
    i++;
  }
  if (name_len == 0) {
    return 0;
  }
  if (name_len == 8 &&
      name_in[i] != '\0' && name_in[i] != '.' &&
      !jc_dos_is_space(name_in[i])) {
    return 0;
  }
  while (name_len < 8) {
    name_out[name_len++] = 0x20;
  }

  if (name_in[i] == '.') {
    seen_dot = 1;
    i++;
  }
  if (seen_dot) {
    for (ext_len = 0; ext_len < 3; ++ext_len) {
      char c = name_in[i];
      if (c == '\0' || jc_dos_is_space(c)) {
        break;
      }
      c = (char)jc_fs_to_upper((jc_u8)c);
      if (!jc_fs_is_valid_char((jc_u8)c)) {
        return 0;
      }
      ext_out[ext_len] = (jc_u8)c;
      i++;
    }
    if (ext_len == 3 &&
        name_in[i] != '\0' && !jc_dos_is_space(name_in[i])) {
      return 0;
    }
  }
  while (ext_len < 3) {
    ext_out[ext_len++] = 0x20;
  }

  while (name_in[i] != '\0') {
    if (!jc_dos_is_space(name_in[i])) {
      return 0;
    }
    i++;
  }

  return 1;
}

static int jc_fs_name_equal(const jc_u8 name_a[8], const jc_u8 ext_a[3],
                            const jc_u8 name_b[8], const jc_u8 ext_b[3]) {
  jc_u32 i;
  for (i = 0; i < 8; ++i) {
    if (name_a[i] != name_b[i]) {
      return 0;
    }
  }
  for (i = 0; i < 3; ++i) {
    if (ext_a[i] != ext_b[i]) {
      return 0;
    }
  }
  return 1;
}

static void jc_fs_mark_block(jc_u16 block, int used) {
  jc_u16 adj = (jc_u16)(block - 1u);
  jc_u32 index = (jc_u32)adj / 8u;
  jc_u8 bit = (jc_u8)(1u << (adj & 7u));
  if (index >= g_fs.alloc_map_bytes) {
    return;
  }
  if (used) {
    g_fs.alloc_map[index] |= bit;
  } else {
    g_fs.alloc_map[index] &= (jc_u8)~bit;
  }
}

static int jc_fs_block_used(jc_u16 block) {
  jc_u16 adj = (jc_u16)(block - 1u);
  jc_u32 index = (jc_u32)adj / 8u;
  jc_u8 bit = (jc_u8)(1u << (adj & 7u));
  if (index >= g_fs.alloc_map_bytes) {
    return 1;
  }
  return (g_fs.alloc_map[index] & bit) != 0;
}

static jc_u16 jc_fs_alloc_block(void) {
  jc_u16 block;
  for (block = 1; block <= (jc_u16)g_fs.alloc_block_count; ++block) {
    if (!jc_fs_block_used(block)) {
      jc_fs_mark_block(block, 1);
      return block;
    }
  }
  return 0;
}

static jc_error_t jc_fs_read_sector(jc_u32 lba, jc_u8 *buf) {
  return jc_cache_blk_read(lba, buf, 1);
}

static jc_error_t jc_fs_write_sector(jc_u32 lba, const jc_u8 *buf) {
  return jc_cache_blk_write(lba, buf, 1);
}

static jc_error_t jc_fs_load_directory(void) {
  jc_u32 i;
  jc_u8 *dir_bytes = (jc_u8 *)g_fs.dir_entries;

  for (i = 0; i < g_fs.dir_sectors_512; ++i) {
    jc_error_t err = jc_fs_read_sector(g_fs.dir_lba_512 + i, g_fs_sector_buf);
    if (err != JC_E_OK) {
      return err;
    }
    if (i * 512u < g_fs.dir_bytes) {
      jc_u32 remaining = g_fs.dir_bytes - i * 512u;
      jc_u32 to_copy = remaining > 512u ? 512u : remaining;
      jc_dos_memcpy(dir_bytes + i * 512u, g_fs_sector_buf, to_copy);
    }
  }
  return JC_E_OK;
}

static jc_error_t jc_fs_flush_directory(void) {
  jc_u32 i;
  jc_u8 *dir_bytes = (jc_u8 *)g_fs.dir_entries;

  if (!g_fs.dir_dirty) {
    return JC_E_OK;
  }
  for (i = 0; i < g_fs.dir_sectors_512; ++i) {
    jc_u32 offset = i * 512u;
    jc_u32 remaining = 0;
    jc_u32 to_copy = 0;
    jc_dos_memset(g_fs_sector_buf, 0, sizeof(g_fs_sector_buf));
    if (offset < g_fs.dir_bytes) {
      remaining = g_fs.dir_bytes - offset;
      to_copy = remaining > 512u ? 512u : remaining;
      jc_dos_memcpy(g_fs_sector_buf, dir_bytes + offset, to_copy);
    }
    {
      jc_error_t err = jc_fs_write_sector(g_fs.dir_lba_512 + i,
                                          g_fs_sector_buf);
      if (err != JC_E_OK) {
        return err;
      }
    }
  }
  g_fs.dir_dirty = 0;
  return JC_E_OK;
}

static int jc_fs_entry_valid(const jc_cpmx_dir_entry_v1 *entry,
                             jc_u32 max_records) {
  jc_u32 i;
  if (entry->user == JC_CPMX_USER_FREE) {
    return 1;
  }
  if (entry->user > 15u) {
    return 0;
  }
  if (entry->reserved0 != 0u) {
    return 0;
  }
  if (entry->record_count > max_records) {
    return 0;
  }
  for (i = 0; i < 8; ++i) {
    jc_u8 c = entry->name[i];
    if (c != 0x20 && !jc_fs_is_valid_char(c)) {
      return 0;
    }
  }
  for (i = 0; i < 3; ++i) {
    jc_u8 c = entry->ext[i];
    if (c != 0x20 && !jc_fs_is_valid_char(c)) {
      return 0;
    }
  }
  return 1;
}

static jc_cpmx_dir_entry_v1 *jc_fs_find_entry(const jc_u8 name[8],
                                              const jc_u8 ext[3],
                                              jc_u8 extent) {
  jc_u32 i;
  for (i = 0; i < g_fs.super.dir_entry_count; ++i) {
    jc_cpmx_dir_entry_v1 *entry = &g_fs.dir_entries[i];
    if (entry->user == JC_CPMX_USER_FREE) {
      continue;
    }
    if (entry->extent != extent) {
      continue;
    }
    if (jc_fs_name_equal(entry->name, entry->ext, name, ext)) {
      return entry;
    }
  }
  return 0;
}

static jc_u32 jc_fs_file_size(const jc_u8 name[8], const jc_u8 ext[3]) {
  jc_u32 i;
  jc_u32 size = 0;
  for (i = 0; i < g_fs.super.dir_entry_count; ++i) {
    jc_cpmx_dir_entry_v1 *entry = &g_fs.dir_entries[i];
    if (entry->user == JC_CPMX_USER_FREE) {
      continue;
    }
    if (!jc_fs_name_equal(entry->name, entry->ext, name, ext)) {
      continue;
    }
    size += (jc_u32)entry->record_count * 128u;
  }
  return size;
}

static jc_cpmx_dir_entry_v1 *jc_fs_alloc_entry(const jc_u8 name[8],
                                               const jc_u8 ext[3],
                                               jc_u8 extent) {
  jc_u32 i;
  for (i = 0; i < g_fs.super.dir_entry_count; ++i) {
    jc_cpmx_dir_entry_v1 *entry = &g_fs.dir_entries[i];
    if (entry->user == JC_CPMX_USER_FREE) {
      jc_dos_memset(entry, 0, sizeof(*entry));
      entry->user = 0;
      jc_dos_memcpy(entry->name, name, 8);
      jc_dos_memcpy(entry->ext, ext, 3);
      entry->extent = extent;
      g_fs.dir_dirty = 1;
      return entry;
    }
  }
  return 0;
}

static void jc_fs_free_entry(jc_cpmx_dir_entry_v1 *entry) {
  jc_u32 i;
  for (i = 0; i < 8; ++i) {
    if (entry->block_ptrs[i] != 0u) {
      jc_fs_mark_block(entry->block_ptrs[i], 0);
    }
  }
  jc_dos_memset(entry, 0, sizeof(*entry));
  entry->user = JC_CPMX_USER_FREE;
  g_fs.dir_dirty = 1;
}

jc_error_t jc_fs_mount(void) {
  jc_error_t err;
  jc_u32 i;
  jc_u32 max_records;
  jc_u32 total_sectors_bytes;
  jc_u32 alloc_bytes;
  jc_u32 dir_sectors;
  jc_u32 block_bytes;
  jc_dos_arena *fs_arena;

  if (g_fs.mounted) {
    return JC_E_OK;
  }

  fs_arena = jc_dos_arena_fs();
  jc_dos_arena_reset(fs_arena);
  jc_dos_memset(&g_fs, 0, sizeof(g_fs));

  err = jc_bios_block_open(0);
  if (err != JC_E_OK) {
    return err;
  }

  err = jc_fs_read_sector(0, g_fs_sector_buf);
  if (err != JC_E_OK) {
    return err;
  }
  jc_dos_memcpy(&g_fs.super, g_fs_sector_buf, sizeof(g_fs.super));

  if (g_fs.super.signature != JC_MAGIC_CPMX) {
    return JC_E_FS_BAD_SUPER;
  }
  if (g_fs.super.version != JC_CPMX_SUPERBLOCK_V1_VERSION) {
    return JC_E_FS_BAD_SUPER;
  }
  if (g_fs.super.size_bytes != JC_CPMX_SUPERBLOCK_V1_SIZE) {
    return JC_E_FS_BAD_SUPER;
  }
  if (g_fs.super.reserved0 != 0u || g_fs.super.reserved1 != 0u) {
    return JC_E_FS_BAD_SUPER;
  }
  for (i = 0; i < 4; ++i) {
    if (g_fs.super.reserved2[i] != 0u) {
      return JC_E_FS_BAD_SUPER;
    }
  }

  g_fs.sector_size = g_fs.super.sector_size;
  if (g_fs.sector_size < 512u || (g_fs.sector_size & 0x1FFu) != 0u) {
    return JC_E_FS_BAD_SUPER;
  }
  g_fs.sector_units = g_fs.sector_size / 512u;

  g_fs.sectors_per_block = g_fs.super.sectors_per_block;
  if (g_fs.sectors_per_block == 0 ||
      (g_fs.sectors_per_block & (g_fs.sectors_per_block - 1u)) != 0u) {
    return JC_E_FS_BAD_SUPER;
  }

  if (g_fs.sectors_per_block > (0xFFFFFFFFu / g_fs.sector_size)) {
    return JC_E_FS_BAD_SUPER;
  }
  block_bytes = g_fs.sector_size * g_fs.sectors_per_block;
  if (block_bytes == 0u) {
    return JC_E_FS_BAD_SUPER;
  }
  g_fs.block_size = block_bytes;
  g_fs.sectors_per_block_512 = g_fs.sectors_per_block * g_fs.sector_units;
  if (g_fs.sectors_per_block_512 > 0xFFFFu) {
    return JC_E_FS_BAD_SUPER;
  }

  g_fs.dir_bytes = (jc_u32)g_fs.super.dir_entry_count * 32u;
  if (g_fs.super.dir_entry_count == 0u) {
    return JC_E_FS_BAD_SUPER;
  }
  dir_sectors = (g_fs.dir_bytes + g_fs.sector_size - 1u) / g_fs.sector_size;
  g_fs.dir_region_bytes = dir_sectors * g_fs.sector_size;
  g_fs.dir_lba_512 = g_fs.super.dir_start_lba * g_fs.sector_units;
  g_fs.dir_sectors_512 = g_fs.dir_region_bytes / 512u;
  g_fs.data_lba_512 = g_fs.super.data_start_lba * g_fs.sector_units;
  g_fs.alloc_block_count = g_fs.super.alloc_block_count;
  if (g_fs.alloc_block_count > 0xFFFFu) {
    return JC_E_FS_BAD_SUPER;
  }

  if (g_fs.super.total_sectors == 0u) {
    return JC_E_FS_BAD_SUPER;
  }
  if (g_fs.super.data_start_lba < g_fs.super.dir_start_lba) {
    return JC_E_FS_BAD_SUPER;
  }
  if (g_fs.super.dir_start_lba + dir_sectors > g_fs.super.total_sectors) {
    return JC_E_FS_BAD_SUPER;
  }
  if (g_fs.super.data_start_lba > g_fs.super.total_sectors) {
    return JC_E_FS_BAD_SUPER;
  }

  if (g_fs.super.total_sectors > (0xFFFFFFFFu / g_fs.sector_size)) {
    return JC_E_FS_BAD_SUPER;
  }
  total_sectors_bytes = g_fs.super.total_sectors * g_fs.sector_size;
  if (g_fs.alloc_block_count > (0xFFFFFFFFu / g_fs.block_size)) {
    return JC_E_FS_BAD_SUPER;
  }
  alloc_bytes = g_fs.alloc_block_count * g_fs.block_size;
  if (alloc_bytes > total_sectors_bytes) {
    return JC_E_FS_BAD_SUPER;
  }

  {
    jc_u32 crc_expected = g_fs.super.crc32;
    jc_cpmx_superblock_v1 temp = g_fs.super;
    temp.crc32 = 0;
    if (jc_dos_crc32((const jc_u8 *)&temp, sizeof(temp)) != crc_expected) {
      return JC_E_FS_BAD_SUPER;
    }
  }

  g_fs.dir_entries = (jc_cpmx_dir_entry_v1 *)jc_dos_arena_alloc(
      fs_arena,
      (jc_u32)g_fs.super.dir_entry_count * sizeof(jc_cpmx_dir_entry_v1), 2);
  if (!g_fs.dir_entries) {
    return JC_E_FS_BAD_SUPER;
  }

  g_fs.alloc_map_bytes = (g_fs.alloc_block_count + 7u) / 8u;
  g_fs.alloc_map = (jc_u8 *)jc_dos_arena_alloc(fs_arena,
                                               g_fs.alloc_map_bytes, 1);
  if (!g_fs.alloc_map) {
    return JC_E_FS_BAD_SUPER;
  }
  jc_dos_memset(g_fs.alloc_map, 0, g_fs.alloc_map_bytes);

  g_fs.block_buf = (jc_u8 *)jc_dos_arena_alloc(fs_arena, g_fs.block_size, 1);
  if (!g_fs.block_buf) {
    return JC_E_FS_BAD_SUPER;
  }

  err = jc_fs_load_directory();
  if (err != JC_E_OK) {
    return err;
  }

  max_records = (g_fs.block_size * 8u) / 128u;
  for (i = 0; i < g_fs.super.dir_entry_count; ++i) {
    jc_cpmx_dir_entry_v1 *entry = &g_fs.dir_entries[i];
    if (!jc_fs_entry_valid(entry, max_records)) {
      return JC_E_FS_BAD_DIR;
    }
    if (entry->user == JC_CPMX_USER_FREE) {
      continue;
    }
    {
      jc_u32 b;
      for (b = 0; b < 8; ++b) {
        jc_u16 block = entry->block_ptrs[b];
        if (block == 0) {
          continue;
        }
        if (block > g_fs.alloc_block_count) {
          return JC_E_FS_BAD_DIR;
        }
        if (jc_fs_block_used(block)) {
          return JC_E_FS_BAD_DIR;
        }
        jc_fs_mark_block(block, 1);
      }
    }
  }

  g_fs.mounted = 1;
  return JC_E_OK;
}

jc_error_t jc_fs_list(jc_fs_list_cb cb, void *ctx) {
  jc_u32 i;
  jc_error_t err = jc_fs_mount();
  if (err != JC_E_OK) {
    return err;
  }
  if (!cb) {
    return JC_E_INTERNAL_ASSERT;
  }
  for (i = 0; i < g_fs.super.dir_entry_count; ++i) {
    jc_cpmx_dir_entry_v1 *entry = &g_fs.dir_entries[i];
    jc_fs_file_info info;
    jc_u32 j;
    int seen = 0;
    if (entry->user == JC_CPMX_USER_FREE) {
      continue;
    }
    if (entry->extent != 0u) {
      continue;
    }
    for (j = 0; j < i; ++j) {
      jc_cpmx_dir_entry_v1 *prev = &g_fs.dir_entries[j];
      if (prev->user == JC_CPMX_USER_FREE) {
        continue;
      }
      if (prev->extent != 0u) {
        continue;
      }
      if (jc_fs_name_equal(prev->name, prev->ext, entry->name, entry->ext)) {
        seen = 1;
        break;
      }
    }
    if (seen) {
      continue;
    }
    jc_dos_memcpy(info.name, entry->name, 8);
    jc_dos_memcpy(info.ext, entry->ext, 3);
    info.flags = entry->flags;
    info.size_bytes = jc_fs_file_size(entry->name, entry->ext);
    cb(&info, ctx);
  }
  return JC_E_OK;
}

jc_error_t jc_fs_open(jc_fs_handle *handle, const char *name, jc_u8 mode) {
  jc_u8 name_buf[8];
  jc_u8 ext_buf[3];
  jc_cpmx_dir_entry_v1 *entry0;
  jc_error_t err;

  if (!handle) {
    return JC_E_INTERNAL_ASSERT;
  }
  err = jc_fs_mount();
  if (err != JC_E_OK) {
    return err;
  }
  if (!jc_fs_parse_name(name, name_buf, ext_buf)) {
    return JC_E_FS_NOT_FOUND;
  }

  entry0 = jc_fs_find_entry(name_buf, ext_buf, 0);
  if (!entry0 && (mode & JC_FS_MODE_WRITE) != 0u &&
      (mode & JC_FS_MODE_CREATE) != 0u) {
    entry0 = jc_fs_alloc_entry(name_buf, ext_buf, 0);
    if (!entry0) {
      return JC_E_FS_NO_SPACE;
    }
  } else if (!entry0) {
    return JC_E_FS_NOT_FOUND;
  }

  if ((mode & JC_FS_MODE_TRUNC) != 0u) {
    jc_error_t del_err = jc_fs_delete(name);
    if (del_err != JC_E_OK && del_err != JC_E_FS_NOT_FOUND) {
      return del_err;
    }
    entry0 = jc_fs_alloc_entry(name_buf, ext_buf, 0);
    if (!entry0) {
      return JC_E_FS_NO_SPACE;
    }
  }

  jc_dos_memset(handle, 0, sizeof(*handle));
  handle->mode = mode;
  jc_dos_memcpy(handle->name, name_buf, 8);
  jc_dos_memcpy(handle->ext, ext_buf, 3);
  handle->pos = 0;
  handle->size_bytes = jc_fs_file_size(name_buf, ext_buf);
  return JC_E_OK;
}

jc_error_t jc_fs_read(jc_fs_handle *handle, jc_u8 *buf, jc_u32 len,
                      jc_u32 *out_read) {
  jc_u32 remaining;
  jc_u32 total_read = 0;
  jc_error_t err;

  if (!handle || !buf) {
    return JC_E_INTERNAL_ASSERT;
  }
  if ((handle->mode & JC_FS_MODE_READ) == 0u) {
    return JC_E_DEV_UNSUPPORTED;
  }
  if (handle->pos >= handle->size_bytes) {
    if (out_read) {
      *out_read = 0;
    }
    return JC_E_OK;
  }
  remaining = handle->size_bytes - handle->pos;
  if (len < remaining) {
    remaining = len;
  }

  while (remaining > 0) {
    jc_u32 block_index = handle->pos / g_fs.block_size;
    jc_u32 block_offset = handle->pos % g_fs.block_size;
    jc_u8 extent = (jc_u8)(block_index / 8u);
    jc_u8 block_in_extent = (jc_u8)(block_index % 8u);
    jc_cpmx_dir_entry_v1 *entry =
        jc_fs_find_entry(handle->name, handle->ext, extent);
    if (!entry) {
      break;
    }
    if (entry->block_ptrs[block_in_extent] == 0u) {
      break;
    }
    {
      jc_u32 lba = g_fs.data_lba_512 +
                   (jc_u32)(entry->block_ptrs[block_in_extent] - 1u) *
                       g_fs.sectors_per_block_512;
      err = jc_bios_block_read(lba, g_fs.block_buf,
                               (jc_u16)g_fs.sectors_per_block_512);
      if (err != JC_E_OK) {
        return err;
      }
      {
        jc_u32 to_copy = g_fs.block_size - block_offset;
        if (to_copy > remaining) {
          to_copy = remaining;
        }
        jc_dos_memcpy(buf + total_read, g_fs.block_buf + block_offset,
                      to_copy);
        handle->pos += to_copy;
        total_read += to_copy;
        remaining -= to_copy;
      }
    }
  }
  if (out_read) {
    *out_read = total_read;
  }
  return JC_E_OK;
}

jc_error_t jc_fs_write(jc_fs_handle *handle, const jc_u8 *buf, jc_u32 len,
                       jc_u32 *out_written) {
  jc_u32 remaining = len;
  jc_u32 total_written = 0;
  jc_error_t err;

  if (!handle || !buf) {
    return JC_E_INTERNAL_ASSERT;
  }
  if ((handle->mode & JC_FS_MODE_WRITE) == 0u) {
    return JC_E_DEV_UNSUPPORTED;
  }

  while (remaining > 0) {
    jc_u32 block_index = handle->pos / g_fs.block_size;
    jc_u32 block_offset = handle->pos % g_fs.block_size;
    jc_u8 extent = (jc_u8)(block_index / 8u);
    jc_u8 block_in_extent = (jc_u8)(block_index % 8u);
    jc_cpmx_dir_entry_v1 *entry =
        jc_fs_find_entry(handle->name, handle->ext, extent);
    if (!entry) {
      entry = jc_fs_alloc_entry(handle->name, handle->ext, extent);
      if (!entry) {
        return JC_E_FS_NO_SPACE;
      }
    }
    if (entry->block_ptrs[block_in_extent] == 0u) {
      jc_u16 block = jc_fs_alloc_block();
      if (block == 0u) {
        return JC_E_FS_NO_SPACE;
      }
      entry->block_ptrs[block_in_extent] = block;
      g_fs.dir_dirty = 1;
      jc_dos_memset(g_fs.block_buf, 0, g_fs.block_size);
    } else {
      jc_u32 lba = g_fs.data_lba_512 +
                   (jc_u32)(entry->block_ptrs[block_in_extent] - 1u) *
                       g_fs.sectors_per_block_512;
      err = jc_bios_block_read(lba, g_fs.block_buf,
                               (jc_u16)g_fs.sectors_per_block_512);
      if (err != JC_E_OK) {
        return err;
      }
    }

    {
      jc_u32 to_copy = g_fs.block_size - block_offset;
      jc_u32 extent_bytes;
      jc_u32 max_records;
      jc_u32 needed_records;
      jc_u32 lba;
      if (to_copy > remaining) {
        to_copy = remaining;
      }
      jc_dos_memcpy(g_fs.block_buf + block_offset, buf + total_written,
                    to_copy);

      lba = g_fs.data_lba_512 +
            (jc_u32)(entry->block_ptrs[block_in_extent] - 1u) *
                g_fs.sectors_per_block_512;
      err = jc_bios_block_write(lba, g_fs.block_buf,
                                (jc_u16)g_fs.sectors_per_block_512);
      if (err != JC_E_OK) {
        return err;
      }

      extent_bytes = block_in_extent * g_fs.block_size + block_offset +
                     to_copy;
      max_records = (g_fs.block_size * 8u) / 128u;
      needed_records = (extent_bytes + 127u) / 128u;
      if (needed_records > max_records) {
        needed_records = max_records;
      }
      if (needed_records > entry->record_count) {
        entry->record_count = (jc_u8)needed_records;
        g_fs.dir_dirty = 1;
      }

      handle->pos += to_copy;
      total_written += to_copy;
      remaining -= to_copy;
      if (handle->pos > handle->size_bytes) {
        handle->size_bytes = handle->pos;
      }
    }
  }

  if (out_written) {
    *out_written = total_written;
  }
  return JC_E_OK;
}

jc_error_t jc_fs_close(jc_fs_handle *handle) {
  if (!handle) {
    return JC_E_INTERNAL_ASSERT;
  }
  return jc_fs_flush_directory();
}

jc_error_t jc_fs_delete(const char *name) {
  jc_u8 name_buf[8];
  jc_u8 ext_buf[3];
  jc_u32 i;
  int found = 0;
  jc_error_t err = jc_fs_mount();
  if (err != JC_E_OK) {
    return err;
  }
  if (!jc_fs_parse_name(name, name_buf, ext_buf)) {
    return JC_E_FS_NOT_FOUND;
  }
  for (i = 0; i < g_fs.super.dir_entry_count; ++i) {
    jc_cpmx_dir_entry_v1 *entry = &g_fs.dir_entries[i];
    if (entry->user == JC_CPMX_USER_FREE) {
      continue;
    }
    if (!jc_fs_name_equal(entry->name, entry->ext, name_buf, ext_buf)) {
      continue;
    }
    jc_fs_free_entry(entry);
    found = 1;
  }
  if (!found) {
    return JC_E_FS_NOT_FOUND;
  }
  return jc_fs_flush_directory();
}

jc_error_t jc_fs_rename(const char *old_name, const char *new_name) {
  jc_u8 old_buf[8];
  jc_u8 old_ext[3];
  jc_u8 new_buf[8];
  jc_u8 new_ext[3];
  jc_u32 i;
  int found = 0;
  jc_error_t err = jc_fs_mount();
  if (err != JC_E_OK) {
    return err;
  }
  if (!jc_fs_parse_name(old_name, old_buf, old_ext)) {
    return JC_E_FS_NOT_FOUND;
  }
  if (!jc_fs_parse_name(new_name, new_buf, new_ext)) {
    return JC_E_FS_NOT_FOUND;
  }
  if (jc_fs_find_entry(new_buf, new_ext, 0) != 0) {
    return JC_E_FS_BAD_DIR;
  }
  for (i = 0; i < g_fs.super.dir_entry_count; ++i) {
    jc_cpmx_dir_entry_v1 *entry = &g_fs.dir_entries[i];
    if (entry->user == JC_CPMX_USER_FREE) {
      continue;
    }
    if (!jc_fs_name_equal(entry->name, entry->ext, old_buf, old_ext)) {
      continue;
    }
    jc_dos_memcpy(entry->name, new_buf, 8);
    jc_dos_memcpy(entry->ext, new_ext, 3);
    g_fs.dir_dirty = 1;
    found = 1;
  }
  if (!found) {
    return JC_E_FS_NOT_FOUND;
  }
  return jc_fs_flush_directory();
}
