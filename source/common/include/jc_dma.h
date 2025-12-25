#ifndef JC_DMA_H
#define JC_DMA_H

#include "jc_types.h"

void jc_dma_sync_for_device(const void *addr, jc_u32 len);
void jc_dma_sync_for_cpu(const void *addr, jc_u32 len);

#endif /* JC_DMA_H */
