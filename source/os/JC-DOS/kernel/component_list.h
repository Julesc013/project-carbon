#ifndef JC_DOS_COMPONENT_LIST_H
#define JC_DOS_COMPONENT_LIST_H

#include "jc_component.h"
#include "jc_error.h"
#include "jc_types.h"

jc_error_t jc_dos_components_init(void);
int jc_dos_component_ready(jc_u16 id);

#endif /* JC_DOS_COMPONENT_LIST_H */
