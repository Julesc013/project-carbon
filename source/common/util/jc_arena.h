#ifndef JC_ARENA_H
#define JC_ARENA_H

#include "jc_types.h"

typedef struct {
  jc_u8 *base;
  jc_u32 size_bytes;
  jc_u32 offset;
} jc_arena;

void jc_arena_init(jc_arena *arena, void *buffer, jc_u32 size_bytes);
void *jc_arena_alloc(jc_arena *arena, jc_u32 size_bytes, jc_u32 align);
void jc_arena_reset(jc_arena *arena);

#endif /* JC_ARENA_H */
