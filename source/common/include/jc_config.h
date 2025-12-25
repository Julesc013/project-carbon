#ifndef JC_CONFIG_H
#define JC_CONFIG_H

/* Compile-time feature switches (defaults are OFF to preserve v1.0 behavior). */

#ifndef JC_CFG_ENABLE_CACHE
#define JC_CFG_ENABLE_CACHE 0
#endif

#ifndef JC_CFG_ENABLE_FASTMEM
#define JC_CFG_ENABLE_FASTMEM 0
#endif

#ifndef JC_CFG_FASTMEM_CAPS
#define JC_CFG_FASTMEM_CAPS 0u
#endif

#ifndef JC_CFG_ENABLE_MODEUP_ACCEL
#define JC_CFG_ENABLE_MODEUP_ACCEL 0
#endif

#ifndef JC_CFG_ENABLE_CAI
#define JC_CFG_ENABLE_CAI 0
#endif

#ifndef JC_CFG_ENABLE_FPU
#define JC_CFG_ENABLE_FPU 0
#endif

#ifndef JC_CFG_ENABLE_DISPLAY
#define JC_CFG_ENABLE_DISPLAY 1
#endif

#ifndef JC_CFG_SHELL_MINIMAL
#define JC_CFG_SHELL_MINIMAL 0
#endif

#ifndef JC_CFG_ENABLE_CPM_COMPAT
#define JC_CFG_ENABLE_CPM_COMPAT 1
#endif

#ifndef JC_CFG_ENABLE_ROMFS
#define JC_CFG_ENABLE_ROMFS 0
#endif

#ifndef JC_CFG_ENABLE_IRQ
#define JC_CFG_ENABLE_IRQ 0
#endif

#ifndef JC_CFG_ENABLE_STORAGE_DMA
#define JC_CFG_ENABLE_STORAGE_DMA 0
#endif

#ifndef JC_CFG_ENABLE_DISPLAY_BACKENDS
#define JC_CFG_ENABLE_DISPLAY_BACKENDS 0
#endif

#ifndef JC_CFG_ENABLE_DISPLAY_SHADOW
#define JC_CFG_ENABLE_DISPLAY_SHADOW 0
#endif

#ifndef JC_CFG_VERBOSE_HW
#define JC_CFG_VERBOSE_HW 0
#endif

#endif /* JC_CONFIG_H */
