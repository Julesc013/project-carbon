#ifndef JC_DOS_PERSONALITY_H
#define JC_DOS_PERSONALITY_H

#include "jc_error.h"
#include "jc_types.h"

#define JC_PERSONALITY_TIER_NATIVE 0xFFu

typedef struct jc_personality_session jc_personality_session;

jc_error_t jc_personality_open(jc_personality_session **out_session,
                               jc_u8 tier,
                               jc_u16 flags);
jc_error_t jc_personality_exec(jc_personality_session *session,
                               const char *jcom_path,
                               jc_u16 exec_flags,
                               jc_u8 *exit_code);
jc_error_t jc_personality_close(jc_personality_session *session);

void jc_personality_test_force_retmd_fail(int enable);

#endif /* JC_DOS_PERSONALITY_H */
