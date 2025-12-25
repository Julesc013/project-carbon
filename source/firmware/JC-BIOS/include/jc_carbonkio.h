#ifndef JC_CARBONKIO_H
#define JC_CARBONKIO_H

#include "jc_contracts.h"
#include "jc_error.h"
#include "jc_types.h"

typedef struct {
  jc_u32 base;
  jc_u8 use_mmio;
} jc_carbonkio_uart;

typedef struct {
  jc_u32 base;
  jc_u8 use_mmio;
  jc_u32 tick_hz;
} jc_carbonkio_timer;

typedef struct {
  jc_u32 base;
  jc_u8 use_mmio;
} jc_carbonkio_pic;

jc_error_t jc_carbonkio_uart_init(jc_carbonkio_uart *uart,
                                  const jc_bdt_entry_v1 *entry);
jc_error_t jc_carbonkio_uart_getc(jc_carbonkio_uart *uart,
                                  jc_u8 *out,
                                  jc_u64 deadline);
jc_error_t jc_carbonkio_uart_putc(jc_carbonkio_uart *uart,
                                  jc_u8 value,
                                  jc_u64 deadline);

jc_error_t jc_carbonkio_timer_init(jc_carbonkio_timer *timer,
                                   const jc_bdt_entry_v1 *entry);
jc_u64 jc_carbonkio_timer_ticks(jc_carbonkio_timer *timer);

jc_error_t jc_carbonkio_pic_init(jc_carbonkio_pic *pic,
                                 const jc_bdt_entry_v1 *entry);
jc_u32 jc_carbonkio_pic_pending(jc_carbonkio_pic *pic);

#endif /* JC_CARBONKIO_H */
