#ifndef JC_DISCOVERY_H
#define JC_DISCOVERY_H

#include "jc_contracts.h"
#include "jc_error.h"

jc_error_t jc_discovery_init(const jc_bsp_anchor_v1 **anchor_out,
                             const jc_discovery_table_v1 **table_out);

#endif /* JC_DISCOVERY_H */
