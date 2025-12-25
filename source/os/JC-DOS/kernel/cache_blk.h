#ifndef JC_DOS_CACHE_BLK_H
#define JC_DOS_CACHE_BLK_H

#include "jc_error.h"
#include "jc_types.h"

jc_error_t jc_cache_blk_init(void);
void jc_cache_blk_enable(int enable);
int jc_cache_blk_is_enabled(void);
void jc_cache_blk_reset(void);

jc_error_t jc_cache_blk_read(jc_u32 lba, jc_u8 *buf, jc_u16 count512);
jc_error_t jc_cache_blk_write(jc_u32 lba, const jc_u8 *buf, jc_u16 count512);

jc_u32 jc_cache_blk_state_crc(void);

#endif /* JC_DOS_CACHE_BLK_H */
