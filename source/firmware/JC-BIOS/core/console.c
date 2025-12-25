#include "jc_console.h"

#include "jc_bdt.h"
#include "jc_bios.h"
#include "jc_carbonkio.h"
#include "jc_contracts_autogen.h"
#include "jc_irq.h"
#include "jc_timer.h"
#include "jc_util.h"

#define JC_UART_TX_TIMEOUT_TICKS 50000u
#define JC_UART_RX_TIMEOUT_TICKS 10000000u

static jc_carbonkio_uart g_uart;
static int g_console_ready = 0;

jc_error_t jc_console_init(void) {
  const jc_bdt_index *bdt = 0;
  const jc_bdt_entry_v1 *entry = 0;
  jc_error_t err;

  bdt = jc_boot_bdt_index();
  if (!bdt) {
    return JC_E_BDT_BAD_SIZE;
  }
  entry = jc_bdt_find(bdt, JC_DEVCLASS_UART, 0);
  if (!entry) {
    return JC_E_DEV_NOT_FOUND;
  }
  err = jc_carbonkio_uart_init(&g_uart, entry);
  if (err == JC_E_OK) {
    g_console_ready = 1;
    jc_irq_register_uart(&g_uart, entry);
  }
  return err;
}

jc_error_t jc_console_putc(char c) {
  jc_u8 v = (jc_u8)c;
  if (!g_console_ready) {
    return JC_E_DEV_NOT_FOUND;
  }
  if (jc_irq_uart_ready()) {
    return jc_irq_uart_putc(v,
                            jc_timer_deadline_from_now(
                                JC_UART_TX_TIMEOUT_TICKS));
  }
  return jc_carbonkio_uart_putc(
      &g_uart, v,
      jc_timer_deadline_from_now(JC_UART_TX_TIMEOUT_TICKS));
}

jc_error_t jc_console_write(const char *s) {
  jc_u32 i = 0;
  if (!s) {
    return JC_E_INTERNAL_ASSERT;
  }
  while (s[i] != '\0') {
    if (s[i] == '\n') {
      jc_console_putc('\r');
    }
    jc_console_putc(s[i]);
    i++;
  }
  return JC_E_OK;
}

jc_error_t jc_console_write_raw(const char *s) {
  jc_u32 i = 0;
  if (!s) {
    return JC_E_INTERNAL_ASSERT;
  }
  if (!g_console_ready) {
    return JC_E_DEV_NOT_FOUND;
  }
  while (s[i] != '\0') {
    jc_console_putc(s[i]);
    i++;
  }
  return JC_E_OK;
}

jc_error_t jc_console_readline(char *buf, jc_u32 max_len) {
  jc_u32 len = 0;
  if (!g_console_ready) {
    return JC_E_DEV_NOT_FOUND;
  }
  if (!buf || max_len == 0) {
    return JC_E_INTERNAL_ASSERT;
  }
  for (;;) {
    jc_u8 v = 0;
    jc_error_t err;
    if (jc_irq_uart_ready()) {
      err = jc_irq_uart_getc(
          &v, jc_timer_deadline_from_now(JC_UART_RX_TIMEOUT_TICKS));
    } else {
      err = jc_carbonkio_uart_getc(
          &g_uart, &v, jc_timer_deadline_from_now(JC_UART_RX_TIMEOUT_TICKS));
    }
    if (err != JC_E_OK) {
      return err;
    }
    if (v == '\r' || v == '\n') {
      jc_console_write("\r\n");
      break;
    }
    if (v == 0x08 || v == 0x7F) {
      if (len > 0) {
        len--;
        jc_console_write("\b \b");
      }
      continue;
    }
    if (len + 1 < max_len) {
      buf[len++] = (char)v;
      jc_console_putc((char)v);
    }
  }
  buf[len] = '\0';
  return JC_E_OK;
}
