#include <stdio.h>
#include <stdlib.h>
#include <string.h>

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

static int read_file(const char *path, unsigned char **out_buf,
                     size_t *out_len) {
  FILE *fp = fopen(path, "rb");
  long size;
  unsigned char *buf;
  if (!fp) {
    return 0;
  }
  if (fseek(fp, 0, SEEK_END) != 0) {
    fclose(fp);
    return 0;
  }
  size = ftell(fp);
  if (size < 0) {
    fclose(fp);
    return 0;
  }
  if (fseek(fp, 0, SEEK_SET) != 0) {
    fclose(fp);
    return 0;
  }
  buf = (unsigned char *)malloc((size_t)size);
  if (!buf) {
    fclose(fp);
    return 0;
  }
  if (fread(buf, 1, (size_t)size, fp) != (size_t)size) {
    fclose(fp);
    free(buf);
    return 0;
  }
  fclose(fp);
  *out_buf = buf;
  *out_len = (size_t)size;
  return 1;
}

static int parse_hex32(const unsigned char *s, unsigned int *out) {
  unsigned int value = 0;
  unsigned int i;
  for (i = 0; i < 8; ++i) {
    unsigned int v = 0;
    unsigned char c = s[i];
    if (c >= '0' && c <= '9') {
      v = (unsigned int)(c - '0');
    } else if (c >= 'A' && c <= 'F') {
      v = (unsigned int)(c - 'A' + 10u);
    } else {
      return 0;
    }
    value = (value << 4) | v;
  }
  *out = value;
  return 1;
}

static int find_crc_line(const unsigned char *buf, size_t len, size_t *pos) {
  size_t i;
  if (len < 6) {
    return 0;
  }
  for (i = len - 6; i > 0; --i) {
    if (buf[i] == 'C' && buf[i + 1] == 'R' && buf[i + 2] == 'C' &&
        buf[i + 3] == '3' && buf[i + 4] == '2' && buf[i + 5] == ' ') {
      if (i == 0 || buf[i - 1] == '\n') {
        *pos = i;
        return 1;
      }
    }
  }
  if (buf[0] == 'C' && buf[1] == 'R' && buf[2] == 'C' && buf[3] == '3' &&
      buf[4] == '2' && buf[5] == ' ') {
    *pos = 0;
    return 1;
  }
  return 0;
}

static int verify_crc(const unsigned char *buf, size_t len) {
  size_t crc_pos = 0;
  unsigned int expected = 0;
  unsigned int crc = 0;
  if (!find_crc_line(buf, len, &crc_pos)) {
    return 0;
  }
  if (crc_pos + 6 + 8 > len) {
    return 0;
  }
  if (!parse_hex32(buf + crc_pos + 6, &expected)) {
    return 0;
  }
  crc = crc32_init();
  crc = crc32_update(crc, buf, crc_pos);
  crc = crc32_finalize(crc);
  return crc == expected;
}

static void usage(void) {
  fprintf(stderr, "usage: transcript_cmp <golden> <candidate>\n");
}

int main(int argc, char **argv) {
  unsigned char *golden = NULL;
  unsigned char *cand = NULL;
  size_t golden_len = 0;
  size_t cand_len = 0;
  int ok = 1;

  if (argc < 3) {
    usage();
    return 1;
  }
  if (!read_file(argv[1], &golden, &golden_len)) {
    fprintf(stderr, "transcript_cmp: failed to read %s\n", argv[1]);
    return 1;
  }
  if (!read_file(argv[2], &cand, &cand_len)) {
    fprintf(stderr, "transcript_cmp: failed to read %s\n", argv[2]);
    free(golden);
    return 1;
  }

  if (!verify_crc(cand, cand_len)) {
    fprintf(stderr, "transcript_cmp: CRC mismatch\n");
    ok = 0;
  }
  if (golden_len != cand_len ||
      memcmp(golden, cand, golden_len) != 0) {
    fprintf(stderr, "transcript_cmp: transcript mismatch\n");
    ok = 0;
  }

  free(golden);
  free(cand);
  return ok ? 0 : 1;
}
