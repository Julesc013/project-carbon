#ifndef JC_MODE_H
#define JC_MODE_H

#include "jc_contracts.h"
#include "jc_error.h"

jc_error_t jc_mode_init(jc_u8 current_tier, jc_u8 max_tier);
jc_u8 jc_mode_current_tier(void);
jc_error_t jc_modeup_request(jc_mode_abi_v1 *capsule);
jc_error_t jc_retmd_request(void);
jc_error_t jc_mode_self_test(void);

#endif /* JC_MODE_H */
