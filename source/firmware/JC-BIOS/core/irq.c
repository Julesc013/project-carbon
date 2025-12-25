#include "jc_irq.h"

#include "jc_bdt.h"
#include "jc_bios.h"
#include "jc_config.h"
#include "jc_contracts_autogen.h"
#include "jc_ringbuf.h"
#include "jc_timer.h"

#define JC_PIC_IRQ_UART_RX (1u << 0)
#define JC_PIC_IRQ_UART_TX (1u << 1)
#define JC_PIC_IRQ_TIMER0 (1u << 4)

#define JC_IRQ_UART_RX_BUF_SIZE 128u
#define JC_IRQ_UART_TX_BUF_SIZE 128u

static int g_irq_enabled;
static jc_carbonkio_pic g_pic;
static int g_pic_ready;

static jc_carbonkio_uart *g_uart;
static int g_uart_irq_capable;
static jc_ringbuf g_uart_rx;
static jc_ringbuf g_uart_tx;
static jc_u8 g_uart_rx_buf[JC_IRQ_UART_RX_BUF_SIZE];
static jc_u8 g_uart_tx_buf[JC_IRQ_UART_TX_BUF_SIZE];

static jc_carbonkio_timer *g_timer;
static int g_timer_irq_capable;
static jc_u32 g_timer_irq_count;

static jc_u32 g_test_pending;

static void jc_irq_update_pic_enable(void) {
  jc_u32 enable_mask = 0u;
  if (!g_pic_ready) {
    return;
  }
  if (g_uart_irq_capable) {
    enable_mask |= JC_PIC_IRQ_UART_RX | JC_PIC_IRQ_UART_TX;
  }
  if (g_timer_irq_capable) {
    enable_mask |= JC_PIC_IRQ_TIMER0;
  }
  jc_carbonkio_pic_write_mask(&g_pic, 0u);
  jc_carbonkio_pic_write_enable(&g_pic, enable_mask);
}

static void jc_irq_config_uart(void) {
  if (!g_uart || !g_uart_irq_capable) {
    return;
  }
  jc_ringbuf_init(&g_uart_rx, g_uart_rx_buf, JC_IRQ_UART_RX_BUF_SIZE);
  jc_ringbuf_init(&g_uart_tx, g_uart_tx_buf, JC_IRQ_UART_TX_BUF_SIZE);
  jc_carbonkio_uart_set_watermarks(g_uart, 1u, 1u);
}

static void jc_irq_config_timer(void) {
  if (!g_timer || !g_timer_irq_capable) {
    return;
  }
  jc_carbonkio_timer_irq_init(g_timer);
}

jc_error_t jc_irq_init(void) {
  const jc_bdt_index *bdt;
  const jc_bdt_entry_v1 *entry;
  jc_error_t err;

  g_irq_enabled = 0;
  g_pic_ready = 0;
  if (JC_CFG_ENABLE_IRQ == 0) {
    return JC_E_OK;
  }
  bdt = jc_boot_bdt_index();
  if (!bdt) {
    return JC_E_BDT_BAD_SIZE;
  }
  entry = jc_bdt_find(bdt, JC_DEVCLASS_PIC, 0);
  if (!entry) {
    return JC_E_OK;
  }
  if ((entry->caps0 & JC_DEV_COMPAT_IRQ_MASK) == 0u) {
    return JC_E_OK;
  }

  err = jc_carbonkio_pic_init(&g_pic, entry);
  if (err != JC_E_OK) {
    return JC_E_OK;
  }

  g_pic_ready = 1;
  g_irq_enabled = 1;

#if defined(JC_SIM_IRQ_INJECT_SPURIOUS)
  g_test_pending |= 0xFFFFFFFFu;
#endif

  jc_irq_config_uart();
  jc_irq_config_timer();
  jc_irq_update_pic_enable();
  return JC_E_OK;
}

int jc_irq_enabled(void) {
  return g_irq_enabled;
}

int jc_irq_uart_ready(void) {
  return g_irq_enabled && g_uart && g_uart_irq_capable;
}

void jc_irq_register_uart(jc_carbonkio_uart *uart,
                          const jc_bdt_entry_v1 *entry) {
  g_uart = uart;
  g_uart_irq_capable = 0;
  if (entry && (entry->caps0 & JC_DEV_COMPAT_IRQ_MASK) != 0u) {
    g_uart_irq_capable = 1;
  }
  if (g_irq_enabled) {
    jc_irq_config_uart();
    jc_irq_update_pic_enable();
  }
}

void jc_irq_register_timer(jc_carbonkio_timer *timer,
                           const jc_bdt_entry_v1 *entry) {
  g_timer = timer;
  g_timer_irq_capable = 0;
  if (entry && (entry->caps1 & JC_DEV_COMPAT_IRQ_MASK) != 0u) {
    g_timer_irq_capable = 1;
  }
  if (g_irq_enabled) {
    jc_irq_config_timer();
    jc_irq_update_pic_enable();
  }
}

void jc_irq_poll(void) {
  jc_u32 pending;
  if (!g_irq_enabled || !g_pic_ready) {
    return;
  }

  pending = jc_carbonkio_pic_pending(&g_pic);
  if (g_test_pending != 0u) {
    pending |= g_test_pending;
    g_test_pending = 0u;
  }

  if (g_uart && g_uart_irq_capable) {
    for (;;) {
      jc_u8 value = 0;
      if (jc_carbonkio_uart_try_getc(g_uart, &value) != JC_E_OK) {
        break;
      }
      if (!jc_ringbuf_push(&g_uart_rx, value)) {
        break;
      }
    }
    while (jc_carbonkio_uart_tx_ready(g_uart)) {
      jc_u8 value = 0;
      if (!jc_ringbuf_pop(&g_uart_tx, &value)) {
        break;
      }
      jc_carbonkio_uart_try_putc(g_uart, value);
    }
    if (pending & (JC_PIC_IRQ_UART_RX | JC_PIC_IRQ_UART_TX)) {
      jc_carbonkio_pic_ack(&g_pic, pending &
                                     (JC_PIC_IRQ_UART_RX | JC_PIC_IRQ_UART_TX));
    }
  }

  if (g_timer && g_timer_irq_capable) {
    if (pending & JC_PIC_IRQ_TIMER0) {
      if (jc_carbonkio_timer_irq_poll(g_timer)) {
        g_timer_irq_count++;
      }
      jc_carbonkio_pic_ack(&g_pic, JC_PIC_IRQ_TIMER0);
    }
  }
}

jc_error_t jc_irq_uart_putc(jc_u8 value, jc_u64 deadline) {
  if (!jc_irq_uart_ready()) {
    return JC_E_DEV_NOT_FOUND;
  }
  while (!jc_timer_expired(deadline)) {
    if (jc_ringbuf_push(&g_uart_tx, value)) {
      jc_irq_poll();
      return JC_E_OK;
    }
    jc_irq_poll();
  }
  return JC_E_DEV_IO_TIMEOUT;
}

jc_error_t jc_irq_uart_getc(jc_u8 *out, jc_u64 deadline) {
  if (!jc_irq_uart_ready() || !out) {
    return JC_E_DEV_NOT_FOUND;
  }
  while (!jc_timer_expired(deadline)) {
    jc_u8 value = 0;
    if (jc_ringbuf_pop(&g_uart_rx, &value)) {
      *out = value;
      return JC_E_OK;
    }
    jc_irq_poll();
  }
  return JC_E_DEV_IO_TIMEOUT;
}

void jc_irq_test_inject_pending(jc_u32 mask) {
  g_test_pending |= mask;
}

jc_u32 jc_irq_timer_irq_count(void) {
  return g_timer_irq_count;
}
