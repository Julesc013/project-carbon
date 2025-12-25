#ifndef JC_DISPLAY_H
#define JC_DISPLAY_H

#include "jc_error.h"
#include "jc_types.h"

#define JC_DISPLAY_TEXT_COLS 80u
#define JC_DISPLAY_TEXT_ROWS 25u

#define JC_DISPLAY_CAP_TEXT 0x0001u
#define JC_DISPLAY_CAP_RASTER 0x0002u
#define JC_DISPLAY_CAP_VT100 0x0004u
#define JC_DISPLAY_CAP_LOCAL 0x0008u

#define JC_DISPLAY_CLEAR_ALL 0u
#define JC_DISPLAY_CLEAR_LINE 1u

#define JC_DISPLAY_ATTR_DEFAULT 0x0000u

#define JC_DISPLAY_SUBCLASS_MC6845 0x0100u
#define JC_DISPLAY_SUBCLASS_MDA 0x0101u
#define JC_DISPLAY_SUBCLASS_CGA_EGA_VGA 0x0102u
#define JC_DISPLAY_SUBCLASS_TMS9918 0x0200u
#define JC_DISPLAY_SUBCLASS_V99X8 0x0201u

typedef jc_error_t (*jc_display_putc_fn)(char c);
typedef jc_error_t (*jc_display_puts_fn)(const char *s);

typedef jc_error_t (*jc_display_text_putc_op)(void *ctx, char c);
typedef jc_error_t (*jc_display_text_puts_op)(void *ctx, const char *s);
typedef jc_error_t (*jc_display_text_set_attr_op)(void *ctx, jc_u16 attr);
typedef jc_error_t (*jc_display_text_cursor_op)(void *ctx,
                                                jc_u16 row,
                                                jc_u16 col);
typedef jc_error_t (*jc_display_text_clear_op)(void *ctx, jc_u16 mode);
typedef jc_error_t (*jc_display_text_scroll_op)(void *ctx, jc_s16 rows);

typedef struct {
  jc_display_text_putc_op putc;
  jc_display_text_puts_op puts;
  jc_display_text_set_attr_op set_attr;
  jc_display_text_cursor_op cursor;
  jc_display_text_clear_op clear;
  jc_display_text_scroll_op scroll;
} jc_display_text_ops;

typedef struct {
  const jc_display_text_ops *text_ops;
  const void *raster_ops;
  void *ctx;
  jc_u32 caps;
  const char *name;
} jc_display_backend;

jc_error_t jc_display_init_vt100(jc_display_putc_fn putc_fn,
                                 jc_display_puts_fn puts_fn);
jc_error_t jc_display_set_backend(const jc_display_backend *backend);
const jc_display_backend *jc_display_backend(void);
const char *jc_display_backend_name(void);
int jc_display_is_ready(void);
int jc_display_is_local(void);

jc_error_t jc_display_putc(char c);
jc_error_t jc_display_puts(const char *s);
jc_error_t jc_display_set_attr(jc_u16 attr);
jc_error_t jc_display_cursor(jc_u16 row, jc_u16 col);
jc_error_t jc_display_clear(jc_u16 mode);
jc_error_t jc_display_scroll(jc_s16 rows);

void jc_display_shadow_reset(void);
jc_u32 jc_display_shadow_crc32(void);

#endif /* JC_DISPLAY_H */
