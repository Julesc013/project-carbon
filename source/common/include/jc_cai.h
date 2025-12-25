#ifndef JC_CAI_H
#define JC_CAI_H

#include "jc_contracts.h"
#include "jc_error.h"
#include "jc_types.h"

#define JC_CAI_AUX_MOCK 1u

typedef jc_u64 (*jc_cai_ticks_fn)(void);
typedef jc_u32 (*jc_cai_tick_hz_fn)(void);

typedef jc_error_t (*jc_cai_mock_handler_fn)(const jc_cai_submit_desc_v1 *desc,
                                             jc_cai_comp_rec_v1 *comp,
                                             void *ctx);

void jc_cai_set_timer(jc_cai_ticks_fn ticks_fn, jc_cai_tick_hz_fn hz_fn);

jc_error_t jc_cai_init(const jc_bdt_header_v1 *bdt,
                       const jc_capset_v1 *capset);
void jc_cai_reset(void);
int jc_cai_is_ready(void);
int jc_cai_is_mock(void);
jc_u16 jc_cai_submit_depth(void);

jc_error_t jc_cai_submit(const jc_cai_submit_desc_v1 *desc,
                         jc_u32 timeout_ticks,
                         jc_cai_comp_rec_v1 *out_comp);
jc_error_t jc_cai_submit_nowait(const jc_cai_submit_desc_v1 *desc);

jc_error_t jc_cai_mock_register(jc_cai_mock_handler_fn handler, void *ctx);
void jc_cai_mock_set_stall(int enable);
void jc_cai_mock_set_bad_tag(int enable);

#endif /* JC_CAI_H */
