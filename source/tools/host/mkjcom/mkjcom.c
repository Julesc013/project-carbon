#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "jc_contracts_autogen.h"

#define JCOM_HEADER_SIZE 48u

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

static void usage(void) {
  fprintf(stderr,
          "usage: mkjcom <input> <output> <load_addr> <entry_offset> <bss_size> <min_tier>\n");
}

int main(int argc, char **argv) {
  const char *input_path;
  const char *output_path;
  unsigned long load_addr;
  unsigned long entry_offset;
  unsigned long bss_size;
  unsigned long min_tier;
  FILE *in = NULL;
  FILE *out = NULL;
  long input_size;
  unsigned int crc;
  unsigned char header[JCOM_HEADER_SIZE];
  unsigned char buf[512];
  size_t read_bytes;
  size_t wrote_bytes;

  if (argc < 7) {
    usage();
    return 1;
  }

  input_path = argv[1];
  output_path = argv[2];
  load_addr = strtoul(argv[3], NULL, 0);
  entry_offset = strtoul(argv[4], NULL, 0);
  bss_size = strtoul(argv[5], NULL, 0);
  min_tier = strtoul(argv[6], NULL, 0);

  in = fopen(input_path, "rb");
  if (!in) {
    fprintf(stderr, "mkjcom: failed to open %s\n", input_path);
    return 1;
  }
  if (fseek(in, 0, SEEK_END) != 0) {
    fclose(in);
    return 1;
  }
  input_size = ftell(in);
  if (input_size < 0) {
    fclose(in);
    return 1;
  }
  if (fseek(in, 0, SEEK_SET) != 0) {
    fclose(in);
    return 1;
  }

  memset(header, 0, sizeof(header));
  write_u32_le(header, 0, JC_MAGIC_JCOM);
  write_u16_le(header, 4, JC_JCOM_HEADER_V1_VERSION);
  write_u16_le(header, 6, JC_JCOM_HEADER_V1_SIZE);
  header[8] = (unsigned char)min_tier;
  header[9] = 0;
  write_u16_le(header, 10, 0);
  write_u32_le(header, 12, JC_JCOM_LOAD_FIXED);
  write_u32_le(header, 16, (unsigned int)load_addr);
  write_u32_le(header, 20, 0);
  write_u32_le(header, 24, (unsigned int)entry_offset);
  write_u32_le(header, 28, (unsigned int)bss_size);
  write_u32_le(header, 32, (unsigned int)input_size);
  write_u32_le(header, 36, 0);
  write_u32_le(header, 40, 0);
  write_u32_le(header, 44, 0);

  out = fopen(output_path, "wb+");
  if (!out) {
    fclose(in);
    fprintf(stderr, "mkjcom: failed to open %s\n", output_path);
    return 1;
  }

  if (fwrite(header, 1, sizeof(header), out) != sizeof(header)) {
    fclose(in);
    fclose(out);
    return 1;
  }

  crc = crc32_init();
  crc = crc32_update(crc, header, sizeof(header));

  while ((read_bytes = fread(buf, 1, sizeof(buf), in)) > 0) {
    crc = crc32_update(crc, buf, read_bytes);
    wrote_bytes = fwrite(buf, 1, read_bytes, out);
    if (wrote_bytes != read_bytes) {
      fclose(in);
      fclose(out);
      return 1;
    }
  }

  crc = crc32_finalize(crc);
  write_u32_le(header, 40, crc);
  if (fseek(out, 40, SEEK_SET) != 0) {
    fclose(in);
    fclose(out);
    return 1;
  }
  if (fwrite(&header[40], 1, 4, out) != 4) {
    fclose(in);
    fclose(out);
    return 1;
  }

  fclose(in);
  fclose(out);
  return 0;
}
