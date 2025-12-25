#include "jc_display.h"

#include "jc_config.h"

static jc_display_backend g_backend;
static int g_backend_ready;

static jc_display_putc_fn g_vt100_putc;
static jc_display_puts_fn g_vt100_puts;

#if JC_CFG_ENABLE_DISPLAY_SHADOW
static jc_u16 g_shadow[JC_DISPLAY_TEXT_ROWS][JC_DISPLAY_TEXT_COLS];
static jc_u16 g_shadow_row;
static jc_u16 g_shadow_col;
static jc_u16 g_shadow_attr;
#endif

static jc_error_t jc_vt100_putc(void *ctx, char c) {
  (void)ctx;
  if (!g_vt100_putc) {
    return JC_E_DEV_UNSUPPORTED;
  }
  return g_vt100_putc(c);
}

static jc_error_t jc_vt100_puts(void *ctx, const char *s) {
  (void)ctx;
  if (!g_vt100_puts) {
    return JC_E_DEV_UNSUPPORTED;
  }
  return g_vt100_puts(s);
}

static const jc_display_text_ops g_vt100_ops = {jc_vt100_putc,
                                                jc_vt100_puts,
                                                0,
                                                0,
                                                0,
                                                0};

#if JC_CFG_ENABLE_DISPLAY_SHADOW
static void jc_display_shadow_clear_row(jc_u16 row) {
  jc_u16 col;
  for (col = 0; col < JC_DISPLAY_TEXT_COLS; ++col) {
    g_shadow[row][col] =
        (jc_u16)((g_shadow_attr << 8) | (jc_u16)0x20u);
  }
}

static void jc_display_shadow_scroll_up(jc_u16 rows) {
  jc_u16 r;
  jc_u16 c;
  if (rows >= JC_DISPLAY_TEXT_ROWS) {
    for (r = 0; r < JC_DISPLAY_TEXT_ROWS; ++r) {
      jc_display_shadow_clear_row(r);
    }
    g_shadow_row = 0;
    g_shadow_col = 0;
    return;
  }
  for (r = 0; r < (jc_u16)(JC_DISPLAY_TEXT_ROWS - rows); ++r) {
    for (c = 0; c < JC_DISPLAY_TEXT_COLS; ++c) {
      g_shadow[r][c] = g_shadow[r + rows][c];
    }
  }
  for (r = (jc_u16)(JC_DISPLAY_TEXT_ROWS - rows); r < JC_DISPLAY_TEXT_ROWS;
       ++r) {
    jc_display_shadow_clear_row(r);
  }
  if (g_shadow_row >= rows) {
    g_shadow_row = (jc_u16)(g_shadow_row - rows);
  } else {
    g_shadow_row = 0;
  }
}

static void jc_display_shadow_scroll_down(jc_u16 rows) {
  jc_s16 r;
  jc_u16 c;
  if (rows >= JC_DISPLAY_TEXT_ROWS) {
    for (r = 0; r < JC_DISPLAY_TEXT_ROWS; ++r) {
      jc_display_shadow_clear_row((jc_u16)r);
    }
    g_shadow_row = 0;
    g_shadow_col = 0;
    return;
  }
  for (r = (jc_s16)JC_DISPLAY_TEXT_ROWS - 1; r >= (jc_s16)rows; --r) {
    for (c = 0; c < JC_DISPLAY_TEXT_COLS; ++c) {
      g_shadow[(jc_u16)r][c] = g_shadow[(jc_u16)(r - rows)][c];
    }
  }
  for (r = 0; r < (jc_s16)rows; ++r) {
    jc_display_shadow_clear_row((jc_u16)r);
  }
  if (g_shadow_row + rows < JC_DISPLAY_TEXT_ROWS) {
    g_shadow_row = (jc_u16)(g_shadow_row + rows);
  } else {
    g_shadow_row = (jc_u16)(JC_DISPLAY_TEXT_ROWS - 1u);
  }
}

static void jc_display_shadow_putc(char c) {
  if (c == '\r') {
    g_shadow_col = 0;
    return;
  }
  if (c == '\n') {
    g_shadow_row++;
    if (g_shadow_row >= JC_DISPLAY_TEXT_ROWS) {
      jc_display_shadow_scroll_up(1);
      g_shadow_row = (jc_u16)(JC_DISPLAY_TEXT_ROWS - 1u);
    }
    return;
  }
  g_shadow[g_shadow_row][g_shadow_col] =
      (jc_u16)((g_shadow_attr << 8) | (jc_u16)(jc_u8)c);
  g_shadow_col++;
  if (g_shadow_col >= JC_DISPLAY_TEXT_COLS) {
    g_shadow_col = 0;
    g_shadow_row++;
    if (g_shadow_row >= JC_DISPLAY_TEXT_ROWS) {
      jc_display_shadow_scroll_up(1);
      g_shadow_row = (jc_u16)(JC_DISPLAY_TEXT_ROWS - 1u);
    }
  }
}

static void jc_display_shadow_puts(const char *s) {
  jc_u32 i = 0;
  if (!s) {
    return;
  }
  while (s[i] != '\0') {
    jc_display_shadow_putc(s[i]);
    i++;
  }
}

static void jc_display_shadow_set_attr(jc_u16 attr) {
  g_shadow_attr = attr;
}

static void jc_display_shadow_cursor(jc_u16 row, jc_u16 col) {
  if (row >= JC_DISPLAY_TEXT_ROWS) {
    row = (jc_u16)(JC_DISPLAY_TEXT_ROWS - 1u);
  }
  if (col >= JC_DISPLAY_TEXT_COLS) {
    col = (jc_u16)(JC_DISPLAY_TEXT_COLS - 1u);
  }
  g_shadow_row = row;
  g_shadow_col = col;
}

static void jc_display_shadow_clear(jc_u16 mode) {
  jc_u16 r;
  if (mode == JC_DISPLAY_CLEAR_LINE) {
    jc_display_shadow_clear_row(g_shadow_row);
    return;
  }
  for (r = 0; r < JC_DISPLAY_TEXT_ROWS; ++r) {
    jc_display_shadow_clear_row(r);
  }
  g_shadow_row = 0;
  g_shadow_col = 0;
}

static void jc_display_shadow_scroll(jc_s16 rows) {
  if (rows > 0) {
    jc_display_shadow_scroll_up((jc_u16)rows);
  } else if (rows < 0) {
    jc_display_shadow_scroll_down((jc_u16)(-rows));
  }
}

static jc_u32 jc_display_crc32_init(void) {
  return 0xFFFFFFFFu;
}

static jc_u32 jc_display_crc32_update(jc_u32 crc,
                                      const jc_u8 *data,
                                      jc_u32 len) {
  jc_u32 i;
  jc_u32 j;
  for (i = 0; i < len; ++i) {
    jc_u32 byte = (jc_u32)data[i];
    crc ^= byte;
    for (j = 0; j < 8; ++j) {
      jc_u32 mask = (crc & 1u) ? 0xEDB88320u : 0u;
      crc = (crc >> 1) ^ mask;
    }
  }
  return crc;
}

static jc_u32 jc_display_crc32_finalize(jc_u32 crc) {
  return crc ^ 0xFFFFFFFFu;
}
#endif

jc_error_t jc_display_init_vt100(jc_display_putc_fn putc_fn,
                                 jc_display_puts_fn puts_fn) {
  jc_display_backend backend;
  if (!putc_fn || !puts_fn) {
    return JC_E_INTERNAL_ASSERT;
  }
  g_vt100_putc = putc_fn;
  g_vt100_puts = puts_fn;
  backend.text_ops = &g_vt100_ops;
  backend.raster_ops = 0;
  backend.ctx = 0;
  backend.caps = JC_DISPLAY_CAP_TEXT | JC_DISPLAY_CAP_VT100;
  backend.name = "VT100";
  return jc_display_set_backend(&backend);
}

jc_error_t jc_display_set_backend(const jc_display_backend *backend) {
  if (!backend || !backend->text_ops) {
    return JC_E_INTERNAL_ASSERT;
  }
  g_backend = *backend;
  g_backend_ready = 1;
  jc_display_shadow_reset();
  return JC_E_OK;
}

const jc_display_backend *jc_display_backend(void) {
  if (!g_backend_ready) {
    return 0;
  }
  return &g_backend;
}

const char *jc_display_backend_name(void) {
  if (!g_backend_ready || !g_backend.name) {
    return "NONE";
  }
  return g_backend.name;
}

int jc_display_is_ready(void) {
  return g_backend_ready != 0;
}

int jc_display_is_local(void) {
  if (!g_backend_ready) {
    return 0;
  }
  return (g_backend.caps & JC_DISPLAY_CAP_LOCAL) != 0u;
}

jc_error_t jc_display_putc(char c) {
  jc_error_t err;
  if (!g_backend_ready || !g_backend.text_ops ||
      !g_backend.text_ops->putc) {
    return JC_E_DEV_UNSUPPORTED;
  }
  err = g_backend.text_ops->putc(g_backend.ctx, c);
#if JC_CFG_ENABLE_DISPLAY_SHADOW
  if (err == JC_E_OK) {
    jc_display_shadow_putc(c);
  }
#endif
  return err;
}

jc_error_t jc_display_puts(const char *s) {
  jc_error_t err = JC_E_OK;
  if (!g_backend_ready || !g_backend.text_ops) {
    return JC_E_DEV_UNSUPPORTED;
  }
  if (!s) {
    return JC_E_INTERNAL_ASSERT;
  }
  if (g_backend.text_ops->puts) {
    err = g_backend.text_ops->puts(g_backend.ctx, s);
  } else if (g_backend.text_ops->putc) {
    jc_u32 i = 0;
    for (;;) {
      char c = s[i];
      if (c == '\0') {
        break;
      }
      err = g_backend.text_ops->putc(g_backend.ctx, c);
      if (err != JC_E_OK) {
        break;
      }
      i++;
    }
  } else {
    return JC_E_DEV_UNSUPPORTED;
  }
#if JC_CFG_ENABLE_DISPLAY_SHADOW
  if (err == JC_E_OK) {
    jc_display_shadow_puts(s);
  }
#endif
  return err;
}

jc_error_t jc_display_set_attr(jc_u16 attr) {
  jc_error_t err;
  if (!g_backend_ready || !g_backend.text_ops ||
      !g_backend.text_ops->set_attr) {
    return JC_E_DEV_UNSUPPORTED;
  }
  err = g_backend.text_ops->set_attr(g_backend.ctx, attr);
#if JC_CFG_ENABLE_DISPLAY_SHADOW
  if (err == JC_E_OK) {
    jc_display_shadow_set_attr(attr);
  }
#endif
  return err;
}

jc_error_t jc_display_cursor(jc_u16 row, jc_u16 col) {
  jc_error_t err;
  if (!g_backend_ready || !g_backend.text_ops ||
      !g_backend.text_ops->cursor) {
    return JC_E_DEV_UNSUPPORTED;
  }
  err = g_backend.text_ops->cursor(g_backend.ctx, row, col);
#if JC_CFG_ENABLE_DISPLAY_SHADOW
  if (err == JC_E_OK) {
    jc_display_shadow_cursor(row, col);
  }
#endif
  return err;
}

jc_error_t jc_display_clear(jc_u16 mode) {
  jc_error_t err;
  if (!g_backend_ready || !g_backend.text_ops ||
      !g_backend.text_ops->clear) {
    return JC_E_DEV_UNSUPPORTED;
  }
  err = g_backend.text_ops->clear(g_backend.ctx, mode);
#if JC_CFG_ENABLE_DISPLAY_SHADOW
  if (err == JC_E_OK) {
    jc_display_shadow_clear(mode);
  }
#endif
  return err;
}

jc_error_t jc_display_scroll(jc_s16 rows) {
  jc_error_t err;
  if (!g_backend_ready || !g_backend.text_ops ||
      !g_backend.text_ops->scroll) {
    return JC_E_DEV_UNSUPPORTED;
  }
  err = g_backend.text_ops->scroll(g_backend.ctx, rows);
#if JC_CFG_ENABLE_DISPLAY_SHADOW
  if (err == JC_E_OK) {
    jc_display_shadow_scroll(rows);
  }
#endif
  return err;
}

void jc_display_shadow_reset(void) {
#if JC_CFG_ENABLE_DISPLAY_SHADOW
  jc_u16 r;
  g_shadow_attr = JC_DISPLAY_ATTR_DEFAULT;
  g_shadow_row = 0;
  g_shadow_col = 0;
  for (r = 0; r < JC_DISPLAY_TEXT_ROWS; ++r) {
    jc_display_shadow_clear_row(r);
  }
#endif
}

jc_u32 jc_display_shadow_crc32(void) {
#if JC_CFG_ENABLE_DISPLAY_SHADOW
  jc_u32 crc = jc_display_crc32_init();
  const jc_u8 *bytes = (const jc_u8 *)g_shadow;
  crc = jc_display_crc32_update(crc, bytes,
                                (jc_u32)sizeof(g_shadow));
  return jc_display_crc32_finalize(crc);
#else
  return 0;
#endif
}
