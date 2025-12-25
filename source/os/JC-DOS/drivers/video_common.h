#ifndef JC_VIDEO_COMMON_H
#define JC_VIDEO_COMMON_H

#include "jc_contracts.h"

const jc_bdt_entry_v1 *jc_video_find_pio(const jc_bdt_header_v1 *bdt,
                                         jc_u16 subclass_id);

#endif /* JC_VIDEO_COMMON_H */
