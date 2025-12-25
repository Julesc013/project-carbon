#include "jc_ee.h"

#include <stdio.h>

#include "jc_util.h"

static jc_u32 g_crc;

static void ee_emit(const char *s) {
  jc_u32 len;
  if (!s) {
    return;
  }
  len = jc_strlen(s);
  fwrite(s, 1, len, stdout);
  g_crc = jc_crc32_update(g_crc, (const jc_u8 *)s, len);
}

static void ee_emit_line(const char *s) {
  ee_emit(s);
  ee_emit("\n");
}

static void ee_emit_hex_u32(jc_u32 value) {
  char buf[9];
  jc_u32_to_hex(buf, value);
  buf[8] = '\0';
  ee_emit(buf);
}

static int ee_expect(jc_error_t err, jc_error_t expect) {
  return err == expect;
}

int main(void) {
  jc_ee ee;
  jc_error_t err;
  int ok_run = 0;
  int ok_file = 0;
  int ok_console = 0;
  int ok_neg_int = 0;
  int ok_neg_illegal = 0;

  g_crc = jc_crc32_init();
  ee_emit_line("EE_CONFORMANCE DOS86 1.0");

  err = ee_open(&ee, JC_EE_KIND_DOS86);
  if (err == JC_E_DEV_UNSUPPORTED) {
    ee_emit_line("RESULT SKIP");
    g_crc = jc_crc32_finalize(g_crc);
    ee_emit("TRANSCRIPT_CRC32 ");
    ee_emit_hex_u32(g_crc);
    ee_emit("\n");
    return 0;
  }
  if (err != JC_E_OK) {
    ee_emit_line("RESULT FAIL");
    g_crc = jc_crc32_finalize(g_crc);
    ee_emit("TRANSCRIPT_CRC32 ");
    ee_emit_hex_u32(g_crc);
    ee_emit("\n");
    return 0;
  }

  err = ee_load(&ee, "HELLO.EXE");
  ok_run = (err == JC_E_OK) && (ee_run(&ee) == JC_E_OK);
  ee_emit_line(ok_run ? "TEST RUN PASS" : "TEST RUN FAIL");

  err = ee_load(&ee, "FILEIO.EXE");
  ok_file = (err == JC_E_OK);
  ee_emit_line(ok_file ? "TEST FILE_IO PASS" : "TEST FILE_IO FAIL");

  err = ee_load(&ee, "CONSOLE.EXE");
  ok_console = (err == JC_E_OK) && (ee_run(&ee) == JC_E_OK);
  ee_emit_line(ok_console ? "TEST CONSOLE PASS" : "TEST CONSOLE FAIL");

  err = ee_load(&ee, "NEG_UNSUPPORTED");
  ok_neg_int = ee_expect(ee_run(&ee), JC_E_DEV_UNSUPPORTED);
  ee_emit_line(ok_neg_int ? "TEST NEG_UNSUPPORTED PASS"
                           : "TEST NEG_UNSUPPORTED FAIL");

  err = ee_load(&ee, "NEG_ILLEGAL");
  ok_neg_illegal = ee_expect(ee_run(&ee), JC_E_EXEC_BAD_VERSION);
  ee_emit_line(ok_neg_illegal ? "TEST NEG_ILLEGAL PASS"
                              : "TEST NEG_ILLEGAL FAIL");

  ee_close(&ee);

  if (ok_run && ok_file && ok_console && ok_neg_int && ok_neg_illegal) {
    ee_emit_line("RESULT PASS");
  } else {
    ee_emit_line("RESULT FAIL");
  }
  g_crc = jc_crc32_finalize(g_crc);
  ee_emit("TRANSCRIPT_CRC32 ");
  ee_emit_hex_u32(g_crc);
  ee_emit("\n");
  return 0;
}
