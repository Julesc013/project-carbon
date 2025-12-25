#include "jc_arena.h"

void jc_arena_init(jc_arena *arena, void *buffer, jc_u32 size_bytes) {
  if (!arena) {
    return;
  }
  arena->base = (jc_u8 *)buffer;
  arena->size_bytes = size_bytes;
  arena->offset = 0;
}

void *jc_arena_alloc(jc_arena *arena, jc_u32 size_bytes, jc_u32 align) {
  jc_u32 offset;
  jc_u32 aligned;
  if (!arena || !arena->base || size_bytes == 0) {
    return 0;
  }
  if (align == 0) {
    align = 1;
  }
  offset = arena->offset;
  aligned = (offset + (align - 1u)) & ~(align - 1u);
  if (aligned + size_bytes > arena->size_bytes) {
    return 0;
  }
  arena->offset = aligned + size_bytes;
  return arena->base + aligned;
}

void jc_arena_reset(jc_arena *arena) {
  if (!arena) {
    return;
  }
  arena->offset = 0;
}
