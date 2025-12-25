#ifndef JC_CAPSET_H
#define JC_CAPSET_H

#include "jc_bdt.h"
#include "jc_contracts.h"
#include "jc_error.h"

jc_error_t jc_capset_init(jc_capset_v1 *capset,
                          const jc_discovery_table_v1 *discovery,
                          const jc_bdt_index *bdt_index);

#endif /* JC_CAPSET_H */
