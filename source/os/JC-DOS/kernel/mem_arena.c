#include "mem_arena.h"

#define JC_DOS_KERNEL_ARENA_SIZE 4096u
#define JC_DOS_FS_ARENA_SIZE 16384u
#define JC_DOS_SHELL_ARENA_SIZE 4096u

static jc_dos_arena g_kernel_arena;
static jc_dos_arena g_fs_arena;
static jc_dos_arena g_shell_arena;

static jc_u8 g_kernel_buf[JC_DOS_KERNEL_ARENA_SIZE];
static jc_u8 g_fs_buf[JC_DOS_FS_ARENA_SIZE];
static jc_u8 g_shell_buf[JC_DOS_SHELL_ARENA_SIZE];

void jc_dos_arena_init(jc_dos_arena *arena, void *buffer, jc_u32 size_bytes) {
  if (!arena) {
    return;
  }
  arena->base = (jc_u8 *)buffer;
  arena->size_bytes = size_bytes;
  arena->offset = 0;
}

void *jc_dos_arena_alloc(jc_dos_arena *arena, jc_u32 size_bytes,
                         jc_u32 align) {
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

void jc_dos_arena_reset(jc_dos_arena *arena) {
  if (!arena) {
    return;
  }
  arena->offset = 0;
}

void jc_dos_mem_init(void) {
  jc_dos_arena_init(&g_kernel_arena, g_kernel_buf,
                    JC_DOS_KERNEL_ARENA_SIZE);
  jc_dos_arena_init(&g_fs_arena, g_fs_buf, JC_DOS_FS_ARENA_SIZE);
  jc_dos_arena_init(&g_shell_arena, g_shell_buf,
                    JC_DOS_SHELL_ARENA_SIZE);
}

jc_dos_arena *jc_dos_arena_kernel(void) {
  return &g_kernel_arena;
}

jc_dos_arena *jc_dos_arena_fs(void) {
  return &g_fs_arena;
}

jc_dos_arena *jc_dos_arena_shell(void) {
  return &g_shell_arena;
}
