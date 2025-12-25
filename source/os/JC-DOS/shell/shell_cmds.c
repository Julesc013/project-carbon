#include "shell_cmds.h"

#include "bios_services.h"
#include "exec_jcom.h"
#include "fs_api.h"
#include "jc_contracts_autogen.h"
#include "jc_dos_util.h"
#include "log.h"
#include "personality.h"

typedef struct {
  const char *pattern;
} jc_shell_dir_ctx;

static void jc_shell_print_name(const jc_u8 name[8], const jc_u8 ext[3]) {
  int i;
  int end = 7;
  int ext_end = 2;
  while (end >= 0 && name[end] == 0x20) {
    end--;
  }
  for (i = 0; i <= end; ++i) {
    jc_bios_console_putc((char)name[i]);
  }
  while (ext_end >= 0 && ext[ext_end] == 0x20) {
    ext_end--;
  }
  if (ext_end >= 0) {
    jc_bios_console_putc('.');
    for (i = 0; i <= ext_end; ++i) {
      jc_bios_console_putc((char)ext[i]);
    }
  }
}

static void jc_shell_format_name(const jc_u8 name[8], const jc_u8 ext[3],
                                 char *out, jc_u32 out_len) {
  int i;
  int end = 7;
  int ext_end = 2;
  jc_u32 pos = 0;
  while (end >= 0 && name[end] == 0x20) {
    end--;
  }
  for (i = 0; i <= end && pos + 1 < out_len; ++i) {
    out[pos++] = (char)name[i];
  }
  while (ext_end >= 0 && ext[ext_end] == 0x20) {
    ext_end--;
  }
  if (ext_end >= 0 && pos + 1 < out_len) {
    out[pos++] = '.';
    for (i = 0; i <= ext_end && pos + 1 < out_len; ++i) {
      out[pos++] = (char)ext[i];
    }
  }
  out[pos] = '\0';
}

static char jc_shell_to_upper(char c) {
  if (c >= 'a' && c <= 'z') {
    return (char)(c - 'a' + 'A');
  }
  return c;
}

static int jc_shell_match_pattern(const char *pattern,
                                  const jc_fs_file_info *info) {
  char file_name[13];
  char pat_buf[13];
  jc_u32 i = 0;
  const char *star = 0;

  if (!pattern || pattern[0] == '\0') {
    return 1;
  }
  if (pattern[0] == '*' && pattern[1] == '\0') {
    return 1;
  }

  jc_shell_format_name(info->name, info->ext, file_name, sizeof(file_name));
  while (pattern[i] != '\0' && i + 1 < sizeof(pat_buf)) {
    pat_buf[i] = jc_shell_to_upper(pattern[i]);
    i++;
  }
  pat_buf[i] = '\0';

  star = pat_buf;
  while (*star && *star != '*') {
    star++;
  }
  if (*star == '*') {
    if (star[1] != '\0') {
      return 0;
    }
    return jc_dos_strncmp(pat_buf, file_name, (jc_u32)(star - pat_buf)) == 0;
  }
  return jc_dos_strcasecmp(pat_buf, file_name) == 0;
}

static void jc_shell_dir_cb(const jc_fs_file_info *info, void *ctx) {
  const jc_shell_dir_ctx *dir_ctx = (const jc_shell_dir_ctx *)ctx;
  if (!jc_shell_match_pattern(dir_ctx->pattern, info)) {
    return;
  }
  jc_dos_log("FILE ");
  jc_shell_print_name(info->name, info->ext);
  jc_dos_log(" SIZE ");
  jc_dos_log_hex32(info->size_bytes);
  jc_dos_log("\r\n");
}

void jc_shell_cmd_dir(const char *pattern) {
  jc_shell_dir_ctx ctx;
  jc_error_t err;
  ctx.pattern = pattern;
  err = jc_fs_list(jc_shell_dir_cb, &ctx);
  if (err != JC_E_OK) {
    jc_dos_log("DIR FAIL ");
    jc_dos_log_hex16(err);
    jc_dos_log("\r\n");
  }
}

void jc_shell_cmd_type(const char *name) {
  jc_fs_handle handle;
  jc_u8 buf[64];
  jc_error_t err = jc_fs_open(&handle, name, JC_FS_MODE_READ);
  if (err != JC_E_OK) {
    jc_dos_log("TYPE FAIL ");
    jc_dos_log_hex16(err);
    jc_dos_log("\r\n");
    return;
  }
  for (;;) {
    jc_u32 got = 0;
    err = jc_fs_read(&handle, buf, sizeof(buf), &got);
    if (err != JC_E_OK) {
      jc_dos_log("TYPE FAIL ");
      jc_dos_log_hex16(err);
      jc_dos_log("\r\n");
      jc_fs_close(&handle);
      return;
    }
    if (got == 0) {
      break;
    }
    {
      jc_u32 i;
      for (i = 0; i < got; ++i) {
        if (buf[i] == '\n') {
          jc_bios_console_putc('\r');
        }
        jc_bios_console_putc((char)buf[i]);
      }
    }
  }
  jc_dos_log("\r\n");
  jc_fs_close(&handle);
}

void jc_shell_cmd_copy(const char *src, const char *dst) {
  jc_fs_handle in_handle;
  jc_fs_handle out_handle;
  jc_u8 buf[128];
  jc_error_t err = jc_fs_open(&in_handle, src, JC_FS_MODE_READ);
  if (err != JC_E_OK) {
    jc_dos_log("COPY FAIL ");
    jc_dos_log_hex16(err);
    jc_dos_log("\r\n");
    return;
  }
  err = jc_fs_open(&out_handle, dst,
                   JC_FS_MODE_WRITE | JC_FS_MODE_CREATE | JC_FS_MODE_TRUNC);
  if (err != JC_E_OK) {
    jc_dos_log("COPY FAIL ");
    jc_dos_log_hex16(err);
    jc_dos_log("\r\n");
    jc_fs_close(&in_handle);
    return;
  }
  for (;;) {
    jc_u32 got = 0;
    jc_u32 wrote = 0;
    err = jc_fs_read(&in_handle, buf, sizeof(buf), &got);
    if (err != JC_E_OK) {
      jc_dos_log("COPY FAIL ");
      jc_dos_log_hex16(err);
      jc_dos_log("\r\n");
      jc_fs_close(&out_handle);
      jc_fs_close(&in_handle);
      return;
    }
    if (got == 0) {
      break;
    }
    err = jc_fs_write(&out_handle, buf, got, &wrote);
    if (err != JC_E_OK || wrote != got) {
      jc_dos_log("COPY FAIL ");
      jc_dos_log_hex16(err);
      jc_dos_log("\r\n");
      jc_fs_close(&out_handle);
      jc_fs_close(&in_handle);
      return;
    }
  }
  jc_fs_close(&out_handle);
  jc_fs_close(&in_handle);
  jc_dos_log("COPY OK\r\n");
}

void jc_shell_cmd_del(const char *name) {
  jc_error_t err = jc_fs_delete(name);
  if (err == JC_E_OK) {
    jc_dos_log("DEL OK\r\n");
  } else {
    jc_dos_log("DEL FAIL ");
    jc_dos_log_hex16(err);
    jc_dos_log("\r\n");
  }
}

void jc_shell_cmd_ren(const char *old_name, const char *new_name) {
  jc_error_t err = jc_fs_rename(old_name, new_name);
  if (err == JC_E_OK) {
    jc_dos_log("REN OK\r\n");
  } else {
    jc_dos_log("REN FAIL ");
    jc_dos_log_hex16(err);
    jc_dos_log("\r\n");
  }
}

static int jc_shell_parse_run_tier(const char *opt, jc_u8 *out_tier) {
  if (!opt || !out_tier) {
    return 0;
  }
  if (jc_dos_strcasecmp(opt, "/P2") == 0) {
    *out_tier = JC_TIER_Z80_P2;
    return 1;
  }
  if (jc_dos_strcasecmp(opt, "/P3") == 0) {
    *out_tier = JC_TIER_Z80_P3;
    return 1;
  }
  if (jc_dos_strcasecmp(opt, "/NATIVE") == 0) {
    *out_tier = JC_PERSONALITY_TIER_NATIVE;
    return 1;
  }
  return 0;
}

void jc_shell_cmd_run(const char *opt, const char *name) {
  jc_u8 rc = 0;
  jc_error_t err;
  if (opt && opt[0] != '\0') {
    jc_u8 tier = 0;
    jc_personality_session *session = 0;
    if (!jc_shell_parse_run_tier(opt, &tier)) {
      err = JC_E_MODE_INVALID_TARGET;
    } else {
      err = jc_personality_open(&session, tier, 0);
      if (err == JC_E_OK) {
        err = jc_personality_exec(session, name, 0, &rc);
      }
      if (session) {
        jc_error_t close_err = jc_personality_close(session);
        if (err == JC_E_OK && close_err != JC_E_OK) {
          err = close_err;
        }
      }
    }
  } else {
    err = jc_exec_jcom_run(name, &rc);
  }
  if (err == JC_E_OK) {
    jc_dos_log("RUN OK RC ");
    jc_dos_log_hex16(rc);
    jc_dos_log("\r\n");
  } else {
    jc_dos_log("RUN FAIL ");
    jc_dos_log_hex16(err);
    jc_dos_log("\r\n");
  }
}
