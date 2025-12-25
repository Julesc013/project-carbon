#ifndef JC_BLOCK_ROBUST_H
#define JC_BLOCK_ROBUST_H

#include "jc_error.h"
#include "jc_types.h"

#define JC_BLOCK_RETRY_MAX 2u
#define JC_BLOCK_RETRY_BACKOFF_TICKS 1u
#define JC_BLOCK_BAD_SECTOR_MAX 16u

jc_error_t jc_blk_read_robust(jc_u32 lba, jc_u8 *buf, jc_u16 count512);
jc_error_t jc_blk_write_robust(jc_u32 lba,
                               const jc_u8 *buf,
                               jc_u16 count512);

void jc_blk_robust_inject_fail(jc_u32 fail_count, jc_error_t err);
void jc_blk_robust_clear_bad_sectors(void);

#endif /* JC_BLOCK_ROBUST_H */
