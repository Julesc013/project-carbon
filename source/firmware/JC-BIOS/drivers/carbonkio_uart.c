#include "jc_carbonkio.h"

#include "jc_contracts_autogen.h"
#include "jc_timer.h"
#include "jc_util.h"

#define JC_UART_DATA_OFF 0x0000u
#define JC_UART_STATUS_OFF 0x0004u
#define JC_UART_CTRL_OFF 0x0008u
#define JC_UART_WATERMARKS_OFF 0x001Cu

#define JC_UART_STATUS_RX_AVAIL (1u << 0)
#define JC_UART_STATUS_TX_READY (1u << 1)

#define JC_UART_CTRL_ENABLE (1u << 0)
#define JC_UART_CTRL_CLR_ERR (1u << 4)

static jc_u32 jc_mmio_read32(jc_u32 base, jc_u32 off) {
  volatile jc_u32 *reg = (volatile jc_u32 *)(unsigned long)(base + off);
  return *reg;
}

static void jc_mmio_write32(jc_u32 base, jc_u32 off, jc_u32 value) {
  volatile jc_u32 *reg = (volatile jc_u32 *)(unsigned long)(base + off);
  *reg = value;
}

static jc_u8 jc_mmio_read8(jc_u32 base, jc_u32 off) {
  volatile jc_u8 *reg = (volatile jc_u8 *)(unsigned long)(base + off);
  return *reg;
}

static void jc_mmio_write8(jc_u32 base, jc_u32 off, jc_u8 value) {
  volatile jc_u8 *reg = (volatile jc_u8 *)(unsigned long)(base + off);
  *reg = value;
}

int jc_carbonkio_uart_rx_ready(jc_carbonkio_uart *uart) {
  jc_u32 status;
  if (!uart) {
    return 0;
  }
  status = jc_mmio_read32(uart->base, JC_UART_STATUS_OFF);
  return (status & JC_UART_STATUS_RX_AVAIL) != 0u;
}

int jc_carbonkio_uart_tx_ready(jc_carbonkio_uart *uart) {
  jc_u32 status;
  if (!uart) {
    return 0;
  }
  status = jc_mmio_read32(uart->base, JC_UART_STATUS_OFF);
  return (status & JC_UART_STATUS_TX_READY) != 0u;
}

jc_error_t jc_carbonkio_uart_init(jc_carbonkio_uart *uart,
                                  const jc_bdt_entry_v1 *entry) {
  if (!uart || !entry) {
    return JC_E_INTERNAL_ASSERT;
  }
  if (entry->mmio_base.hi != 0u || entry->mmio_base.lo == 0u) {
    return JC_E_DEV_UNSUPPORTED;
  }
  if (entry->mmio_size < 0x0020u) {
    return JC_E_DEV_UNSUPPORTED;
  }
  uart->base = entry->mmio_base.lo;
  uart->use_mmio = 1u;
  jc_mmio_write32(uart->base, JC_UART_CTRL_OFF,
                  (JC_UART_CTRL_ENABLE | JC_UART_CTRL_CLR_ERR));
  return JC_E_OK;
}

jc_error_t jc_carbonkio_uart_getc(jc_carbonkio_uart *uart,
                                  jc_u8 *out,
                                  jc_u64 deadline) {
  if (!uart || !out) {
    return JC_E_INTERNAL_ASSERT;
  }
  while (!jc_timer_expired(deadline)) {
    if (jc_carbonkio_uart_rx_ready(uart)) {
      *out = jc_mmio_read8(uart->base, JC_UART_DATA_OFF);
      return JC_E_OK;
    }
  }
  return JC_E_DEV_IO_TIMEOUT;
}

jc_error_t jc_carbonkio_uart_putc(jc_carbonkio_uart *uart,
                                  jc_u8 value,
                                  jc_u64 deadline) {
  if (!uart) {
    return JC_E_INTERNAL_ASSERT;
  }
  while (!jc_timer_expired(deadline)) {
    if (jc_carbonkio_uart_tx_ready(uart)) {
      jc_mmio_write8(uart->base, JC_UART_DATA_OFF, value);
      return JC_E_OK;
    }
  }
  return JC_E_DEV_IO_TIMEOUT;
}

jc_error_t jc_carbonkio_uart_try_getc(jc_carbonkio_uart *uart, jc_u8 *out) {
  if (!uart || !out) {
    return JC_E_INTERNAL_ASSERT;
  }
  if (!jc_carbonkio_uart_rx_ready(uart)) {
    return JC_E_DEV_IO_TIMEOUT;
  }
  *out = jc_mmio_read8(uart->base, JC_UART_DATA_OFF);
  return JC_E_OK;
}

jc_error_t jc_carbonkio_uart_try_putc(jc_carbonkio_uart *uart, jc_u8 value) {
  if (!uart) {
    return JC_E_INTERNAL_ASSERT;
  }
  if (!jc_carbonkio_uart_tx_ready(uart)) {
    return JC_E_DEV_IO_TIMEOUT;
  }
  jc_mmio_write8(uart->base, JC_UART_DATA_OFF, value);
  return JC_E_OK;
}

jc_error_t jc_carbonkio_uart_set_watermarks(jc_carbonkio_uart *uart,
                                            jc_u8 rx,
                                            jc_u8 tx) {
  jc_u32 value;
  if (!uart) {
    return JC_E_INTERNAL_ASSERT;
  }
  value = (jc_u32)rx | ((jc_u32)tx << 8);
  jc_mmio_write32(uart->base, JC_UART_WATERMARKS_OFF, value);
  return JC_E_OK;
}
