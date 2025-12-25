#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "jc_contracts_autogen.h"

#define SECTOR_SIZE 512u

typedef struct {
  unsigned char name[8];
  unsigned char ext[3];
  const char *path;
  unsigned long size;
} FileSpec;

static unsigned int crc32_init(void) {
  return 0xFFFFFFFFu;
}

static unsigned int crc32_update(unsigned int crc, const unsigned char *data,
                                 size_t len) {
  size_t i;
  for (i = 0; i < len; ++i) {
    unsigned int byte = data[i];
    unsigned int j;
    crc ^= byte;
    for (j = 0; j < 8; ++j) {
      unsigned int mask = (crc & 1u) ? 0xEDB88320u : 0u;
      crc = (crc >> 1) ^ mask;
    }
  }
  return crc;
}

static unsigned int crc32_finalize(unsigned int crc) {
  return crc ^ 0xFFFFFFFFu;
}

static void write_u16_le(unsigned char *buf, unsigned int off,
                         unsigned int value) {
  buf[off] = (unsigned char)(value & 0xFFu);
  buf[off + 1] = (unsigned char)((value >> 8) & 0xFFu);
}

static void write_u32_le(unsigned char *buf, unsigned int off,
                         unsigned int value) {
  buf[off] = (unsigned char)(value & 0xFFu);
  buf[off + 1] = (unsigned char)((value >> 8) & 0xFFu);
  buf[off + 2] = (unsigned char)((value >> 16) & 0xFFu);
  buf[off + 3] = (unsigned char)((value >> 24) & 0xFFu);
}

static int is_valid_char(unsigned char c) {
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

static unsigned char to_upper(unsigned char c) {
  if (c >= 'a' && c <= 'z') {
    return (unsigned char)(c - 'a' + 'A');
  }
  return c;
}

static int parse_name(const char *name_in,
                      unsigned char name_out[8],
                      unsigned char ext_out[3]) {
  unsigned int i = 0;
  unsigned int name_len = 0;
  unsigned int ext_len = 0;
  int seen_dot = 0;

  if (!name_in) {
    return 0;
  }
  while (name_in[i] == ' ' || name_in[i] == '\t') {
    i++;
  }
  if (name_in[i] == '\0') {
    return 0;
  }

  for (name_len = 0; name_len < 8; ++name_len) {
    char c = name_in[i];
    if (c == '\0' || c == '.' || c == ' ' || c == '\t') {
      break;
    }
    c = (char)to_upper((unsigned char)c);
    if (!is_valid_char((unsigned char)c)) {
      return 0;
    }
    name_out[name_len] = (unsigned char)c;
    i++;
  }
  if (name_len == 0) {
    return 0;
  }
  if (name_len == 8 && name_in[i] != '\0' && name_in[i] != '.' &&
      name_in[i] != ' ' && name_in[i] != '\t') {
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
      if (c == '\0' || c == ' ' || c == '\t') {
        break;
      }
      c = (char)to_upper((unsigned char)c);
      if (!is_valid_char((unsigned char)c)) {
        return 0;
      }
      ext_out[ext_len] = (unsigned char)c;
      i++;
    }
    if (ext_len == 3 && name_in[i] != '\0' && name_in[i] != ' ' &&
        name_in[i] != '\t') {
      return 0;
    }
  }
  while (ext_len < 3) {
    ext_out[ext_len++] = 0x20;
  }
  while (name_in[i] != '\0') {
    if (name_in[i] != ' ' && name_in[i] != '\t') {
      return 0;
    }
    i++;
  }
  return 1;
}

static int is_power_of_two(unsigned long v) {
  return v != 0 && (v & (v - 1)) == 0;
}

static void usage(void) {
  fprintf(stderr,
          "usage: mkdisk <output.img> <total_sectors> <dir_entries> <sectors_per_block> <volume_id> [NAME=PATH...]\n");
}

int main(int argc, char **argv) {
  const char *out_path;
  unsigned long total_sectors;
  unsigned long dir_entries;
  unsigned long sectors_per_block;
  unsigned long volume_id;
  unsigned long dir_bytes;
  unsigned long dir_sectors;
  unsigned long data_start_lba;
  unsigned long alloc_block_count;
  unsigned long block_size;
  unsigned char superblock[64];
  unsigned char *dir_region = NULL;
  unsigned char *block_buf = NULL;
  FileSpec *files = NULL;
  int file_count = 0;
  FILE *out = NULL;
  int i;

  if (argc < 6) {
    usage();
    return 1;
  }

  out_path = argv[1];
  total_sectors = strtoul(argv[2], NULL, 0);
  dir_entries = strtoul(argv[3], NULL, 0);
  sectors_per_block = strtoul(argv[4], NULL, 0);
  volume_id = strtoul(argv[5], NULL, 0);

  if (total_sectors == 0 || dir_entries == 0 || sectors_per_block == 0 ||
      !is_power_of_two(sectors_per_block)) {
    usage();
    return 1;
  }

  dir_bytes = dir_entries * 32u;
  dir_sectors = (dir_bytes + SECTOR_SIZE - 1u) / SECTOR_SIZE;
  data_start_lba = 1u + dir_sectors;
  if (data_start_lba >= total_sectors) {
    fprintf(stderr, "mkdisk: total_sectors too small\n");
    return 1;
  }

  alloc_block_count = (total_sectors - data_start_lba) / sectors_per_block;
  if (alloc_block_count == 0) {
    fprintf(stderr, "mkdisk: no alloc blocks available\n");
    return 1;
  }
  if (alloc_block_count > 0xFFFFu) {
    fprintf(stderr, "mkdisk: alloc_block_count too large\n");
    return 1;
  }

  block_size = SECTOR_SIZE * sectors_per_block;
  block_buf = (unsigned char *)malloc(block_size);
  if (!block_buf) {
    return 1;
  }
  memset(block_buf, 0, block_size);

  file_count = argc - 6;
  if (file_count > 0) {
    files = (FileSpec *)calloc((size_t)file_count, sizeof(FileSpec));
    if (!files) {
      free(block_buf);
      return 1;
    }
    for (i = 0; i < file_count; ++i) {
      const char *arg = argv[6 + i];
      char *eq = strchr(arg, '=');
      if (!eq) {
        fprintf(stderr, "mkdisk: bad file arg '%s'\n", arg);
        free(files);
        free(block_buf);
        return 1;
      }
      *eq = '\0';
      if (!parse_name(arg, files[i].name, files[i].ext)) {
        fprintf(stderr, "mkdisk: invalid name '%s'\n", arg);
        free(files);
        free(block_buf);
        return 1;
      }
      files[i].path = eq + 1;
      {
        FILE *in = fopen(files[i].path, "rb");
        long sz;
        if (!in) {
          fprintf(stderr, "mkdisk: failed to open %s\n", files[i].path);
          free(files);
          free(block_buf);
          return 1;
        }
        fseek(in, 0, SEEK_END);
        sz = ftell(in);
        fclose(in);
        if (sz < 0) {
          free(files);
          free(block_buf);
          return 1;
        }
        files[i].size = (unsigned long)sz;
      }
    }
  }

  dir_region = (unsigned char *)malloc(dir_sectors * SECTOR_SIZE);
  if (!dir_region) {
    free(files);
    free(block_buf);
    return 1;
  }
  memset(dir_region, 0, dir_sectors * SECTOR_SIZE);

  for (i = 0; i < (int)dir_entries; ++i) {
    dir_region[i * 32] = (unsigned char)JC_CPMX_USER_FREE;
  }

  memset(superblock, 0, sizeof(superblock));
  write_u32_le(superblock, 0, JC_MAGIC_CPMX);
  write_u16_le(superblock, 4, JC_CPMX_SUPERBLOCK_V1_VERSION);
  write_u16_le(superblock, 6, JC_CPMX_SUPERBLOCK_V1_SIZE);
  write_u16_le(superblock, 8, SECTOR_SIZE);
  write_u16_le(superblock, 10, (unsigned int)sectors_per_block);
  write_u16_le(superblock, 12, (unsigned int)dir_entries);
  write_u16_le(superblock, 14, 0);
  write_u32_le(superblock, 16, (unsigned int)total_sectors);
  write_u32_le(superblock, 20, 1u);
  write_u32_le(superblock, 24, (unsigned int)data_start_lba);
  write_u32_le(superblock, 28, (unsigned int)alloc_block_count);
  write_u32_le(superblock, 32, (unsigned int)volume_id);
  write_u32_le(superblock, 36, 0);
  write_u32_le(superblock, 40, 0);
  write_u32_le(superblock, 44, 0);

  {
    unsigned int crc;
    crc = crc32_init();
    crc = crc32_update(crc, superblock, sizeof(superblock));
    crc = crc32_finalize(crc);
    write_u32_le(superblock, 40, crc);
  }

  out = fopen(out_path, "wb+");
  if (!out) {
    free(dir_region);
    free(files);
    free(block_buf);
    return 1;
  }
  if (fseek(out, (long)(total_sectors * SECTOR_SIZE - 1u), SEEK_SET) != 0) {
    fclose(out);
    free(dir_region);
    free(files);
    free(block_buf);
    return 1;
  }
  fputc(0, out);

  if (fseek(out, 0, SEEK_SET) != 0) {
    fclose(out);
    free(dir_region);
    free(files);
    free(block_buf);
    return 1;
  }
  if (fwrite(superblock, 1, sizeof(superblock), out) != sizeof(superblock)) {
    fclose(out);
    free(dir_region);
    free(files);
    free(block_buf);
    return 1;
  }

  {
    unsigned long next_block = 1;
    unsigned long dir_index = 0;
    for (i = 0; i < file_count; ++i) {
      unsigned long remaining = files[i].size;
      unsigned long extent_bytes = block_size * 8u;
      unsigned long extent = 0;
      FILE *in = fopen(files[i].path, "rb");
      if (!in) {
        fclose(out);
        free(dir_region);
        free(files);
        free(block_buf);
        return 1;
      }
      while (remaining > 0 || extent == 0) {
        unsigned long extent_size = remaining > extent_bytes ? extent_bytes
                                                             : remaining;
        unsigned long record_count =
            (extent_size + 127u) / 128u;
        unsigned char *entry = dir_region + dir_index * 32u;
        unsigned long block_idx;
        if (dir_index >= dir_entries) {
          fclose(in);
          fclose(out);
          free(dir_region);
          free(files);
          free(block_buf);
          return 1;
        }
        entry[0] = 0;
        memcpy(entry + 1, files[i].name, 8);
        memcpy(entry + 9, files[i].ext, 3);
        entry[12] = 0;
        entry[13] = (unsigned char)extent;
        entry[14] = 0;
        entry[15] = (unsigned char)record_count;
        for (block_idx = 0; block_idx < 8; ++block_idx) {
          unsigned long block = 0;
          unsigned long write_size;
          long offset;
          if (remaining == 0) {
            write_u16_le(entry, 16u + block_idx * 2u, 0);
            continue;
          }
          if (next_block > alloc_block_count) {
            fclose(in);
            fclose(out);
            free(dir_region);
            free(files);
            free(block_buf);
            return 1;
          }
          block = next_block++;
          write_u16_le(entry, 16u + block_idx * 2u, (unsigned int)block);

          write_size = remaining > block_size ? block_size : remaining;
          memset(block_buf, 0, block_size);
          if (fread(block_buf, 1, write_size, in) != write_size) {
            fclose(in);
            fclose(out);
            free(dir_region);
            free(files);
            free(block_buf);
            return 1;
          }

          offset = (long)((data_start_lba +
                           (block - 1u) * sectors_per_block) *
                          SECTOR_SIZE);
          if (fseek(out, offset, SEEK_SET) != 0) {
            fclose(in);
            fclose(out);
            free(dir_region);
            free(files);
            free(block_buf);
            return 1;
          }
          if (fwrite(block_buf, 1, block_size, out) != block_size) {
            fclose(in);
            fclose(out);
            free(dir_region);
            free(files);
            free(block_buf);
            return 1;
          }
          remaining -= write_size;
        }
        dir_index++;
        extent++;
        if (remaining == 0) {
          break;
        }
      }
      fclose(in);
    }
  }

  if (fseek(out, (long)(SECTOR_SIZE * 1u), SEEK_SET) != 0) {
    fclose(out);
    free(dir_region);
    free(files);
    free(block_buf);
    return 1;
  }
  if (fwrite(dir_region, 1, dir_sectors * SECTOR_SIZE, out) !=
      dir_sectors * SECTOR_SIZE) {
    fclose(out);
    free(dir_region);
    free(files);
    free(block_buf);
    return 1;
  }

  fclose(out);
  free(dir_region);
  free(files);
  free(block_buf);
  return 0;
}
