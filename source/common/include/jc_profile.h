#ifndef JC_PROFILE_H
#define JC_PROFILE_H

#include "jc_types.h"

#define JC_PROFILE_SUBSYS_FS_CPMX (1u << 0)
#define JC_PROFILE_SUBSYS_FS_ROMFS (1u << 1)
#define JC_PROFILE_SUBSYS_SHELL_FULL (1u << 2)
#define JC_PROFILE_SUBSYS_SHELL_MIN (1u << 3)
#define JC_PROFILE_SUBSYS_CACHE (1u << 4)
#define JC_PROFILE_SUBSYS_FASTMEM (1u << 5)
#define JC_PROFILE_SUBSYS_DISPLAY (1u << 6)
#define JC_PROFILE_SUBSYS_CAI (1u << 7)
#define JC_PROFILE_SUBSYS_FPU (1u << 8)
#define JC_PROFILE_SUBSYS_COMPAT_CPM (1u << 9)

typedef struct {
  jc_u8 profile_id;
  jc_u8 reserved0;
  jc_u16 reserved1;
  const jc_u16 *required_devices;
  jc_u16 required_device_count;
  const jc_u16 *optional_devices;
  jc_u16 optional_device_count;
  jc_u32 max_ram_bytes;
  jc_u32 max_tpa_bytes;
  jc_u32 subsys_mask;
} jc_profile_policy;

const jc_profile_policy *jc_profile_get(jc_u8 profile_id);
int jc_profile_requires_device(const jc_profile_policy *policy,
                               jc_u16 devclass);
int jc_profile_allows_device(const jc_profile_policy *policy,
                             jc_u16 devclass);
int jc_profile_allows_subsys(const jc_profile_policy *policy,
                             jc_u32 subsys_mask);

#endif /* JC_PROFILE_H */
