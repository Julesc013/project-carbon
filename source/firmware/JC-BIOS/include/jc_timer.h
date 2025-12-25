#ifndef JC_TIMER_H
#define JC_TIMER_H

#include "jc_error.h"
#include "jc_types.h"

jc_error_t jc_timer_init(void);
jc_u64 jc_timer_ticks(void);
jc_u32 jc_timer_tick_hz(void);
jc_u64 jc_timer_deadline_from_now(jc_u32 ticks);
int jc_timer_expired(jc_u64 deadline);

#endif /* JC_TIMER_H */
