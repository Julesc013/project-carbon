#ifndef JC_DOS_MEM_ARENA_H
#define JC_DOS_MEM_ARENA_H

#include "jc_types.h"

typedef struct {
  jc_u8 *base;
  jc_u32 size_bytes;
  jc_u32 offset;
} jc_dos_arena;

void jc_dos_mem_init(void);

void jc_dos_arena_init(jc_dos_arena *arena, void *buffer, jc_u32 size_bytes);
void *jc_dos_arena_alloc(jc_dos_arena *arena, jc_u32 size_bytes, jc_u32 align);
void jc_dos_arena_reset(jc_dos_arena *arena);

jc_dos_arena *jc_dos_arena_kernel(void);
jc_dos_arena *jc_dos_arena_fs(void);
jc_dos_arena *jc_dos_arena_shell(void);

#endif /* JC_DOS_MEM_ARENA_H */
