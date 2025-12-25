#ifndef JC_IRQ_H
#define JC_IRQ_H

#include "jc_carbonkio.h"
#include "jc_contracts.h"
#include "jc_error.h"
#include "jc_types.h"

jc_error_t jc_irq_init(void);
int jc_irq_enabled(void);
int jc_irq_uart_ready(void);
void jc_irq_poll(void);

void jc_irq_register_uart(jc_carbonkio_uart *uart,
                          const jc_bdt_entry_v1 *entry);
void jc_irq_register_timer(jc_carbonkio_timer *timer,
                           const jc_bdt_entry_v1 *entry);

jc_error_t jc_irq_uart_putc(jc_u8 value, jc_u64 deadline);
jc_error_t jc_irq_uart_getc(jc_u8 *out, jc_u64 deadline);

void jc_irq_test_inject_pending(jc_u32 mask);
jc_u32 jc_irq_timer_irq_count(void);

#endif /* JC_IRQ_H */
