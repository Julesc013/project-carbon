#ifndef JC_CONSOLE_H
#define JC_CONSOLE_H

#include "jc_error.h"
#include "jc_types.h"

jc_error_t jc_console_init(void);
jc_error_t jc_console_putc(char c);
jc_error_t jc_console_write(const char *s);
jc_error_t jc_console_write_raw(const char *s);
jc_error_t jc_console_readline(char *buf, jc_u32 max_len);

#endif /* JC_CONSOLE_H */
