#ifndef JC_BLOCK_H
#define JC_BLOCK_H

#include "jc_contracts.h"
#include "jc_error.h"
#include "jc_types.h"

typedef struct {
  jc_u32 block_size_bytes;
  jc_u32 max_sectors_per_op;
  jc_u32 total_sectors;
  jc_u32 timeout_ticks;
} jc_block_params;

jc_error_t jc_blk_open(jc_u16 instance);
jc_error_t jc_blk_read(jc_u32 lba, jc_u8 *buf, jc_u16 count512);
jc_error_t jc_blk_write(jc_u32 lba, const jc_u8 *buf, jc_u16 count512);
jc_error_t jc_blk_get_params(jc_block_params *out_params);
jc_error_t jc_blk_self_test(void);
jc_error_t jc_blk_test_timeout(jc_u32 timeout_ticks);

jc_error_t jc_storage_validate_entry(const jc_bdt_entry_v1 *entry);

#endif /* JC_BLOCK_H */
