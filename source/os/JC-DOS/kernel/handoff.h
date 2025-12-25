#ifndef JC_DOS_HANDOFF_LOCAL_H
#define JC_DOS_HANDOFF_LOCAL_H

#include "jc_bios_services.h"
#include "jc_contracts.h"
#include "jc_dos_handoff.h"
#include "jc_error.h"
#include "jc_profile.h"
#include "jc_types.h"

jc_error_t jc_dos_handoff_init(const jc_dos_handoff_v1 *handoff);

const jc_bios_services_v1 *jc_dos_services(void);
const jc_capset_v1 *jc_dos_capset(void);
const jc_bdt_header_v1 *jc_dos_bdt(void);
const jc_profile_policy *jc_dos_profile_policy(void);
jc_u32 jc_dos_tpa_base(void);
jc_u32 jc_dos_tpa_size(void);

#endif /* JC_DOS_HANDOFF_LOCAL_H */
