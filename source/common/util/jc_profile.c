#include "jc_profile.h"

#include "jc_contracts_autogen.h"

static const jc_u16 g_req_cpu_only[] = {
    JC_DEVCLASS_UART,
    JC_DEVCLASS_TIMER,
    JC_DEVCLASS_PIC,
};

static const jc_u16 g_opt_cpu_only[] = {
    JC_DEVCLASS_STORAGE,
};

static const jc_u16 g_req_mcu[] = {
    JC_DEVCLASS_UART,
    JC_DEVCLASS_TIMER,
    JC_DEVCLASS_PIC,
};

static const jc_u16 g_opt_mcu[] = {
    JC_DEVCLASS_STORAGE,
};

static const jc_u16 g_req_soc_retro[] = {
    JC_DEVCLASS_UART,
    JC_DEVCLASS_TIMER,
    JC_DEVCLASS_PIC,
    JC_DEVCLASS_STORAGE,
};

static const jc_u16 g_opt_soc_retro[] = {
    JC_DEVCLASS_ACCEL,
    JC_DEVCLASS_DMA,
};

static const jc_u16 g_req_soc_workstation[] = {
    JC_DEVCLASS_UART,
    JC_DEVCLASS_TIMER,
    JC_DEVCLASS_PIC,
    JC_DEVCLASS_STORAGE,
};

static const jc_u16 g_opt_soc_workstation[] = {
    JC_DEVCLASS_ACCEL,
    JC_DEVCLASS_DMA,
};

static const jc_profile_policy g_profiles[] = {
    {JC_PROFILE_CPU_ONLY,
     0,
     0,
     g_req_cpu_only,
     (jc_u16)(sizeof(g_req_cpu_only) / sizeof(g_req_cpu_only[0])),
     g_opt_cpu_only,
     (jc_u16)(sizeof(g_opt_cpu_only) / sizeof(g_opt_cpu_only[0])),
     0,
     0,
     (JC_PROFILE_SUBSYS_FS_CPMX | JC_PROFILE_SUBSYS_FS_ROMFS |
      JC_PROFILE_SUBSYS_SHELL_MIN | JC_PROFILE_SUBSYS_FASTMEM)},
    {JC_PROFILE_MCU,
     0,
     0,
     g_req_mcu,
     (jc_u16)(sizeof(g_req_mcu) / sizeof(g_req_mcu[0])),
     g_opt_mcu,
     (jc_u16)(sizeof(g_opt_mcu) / sizeof(g_opt_mcu[0])),
     0,
     0,
     (JC_PROFILE_SUBSYS_FS_CPMX | JC_PROFILE_SUBSYS_FS_ROMFS |
      JC_PROFILE_SUBSYS_SHELL_MIN | JC_PROFILE_SUBSYS_FASTMEM)},
    {JC_PROFILE_SOC_RETRO,
     0,
     0,
     g_req_soc_retro,
     (jc_u16)(sizeof(g_req_soc_retro) / sizeof(g_req_soc_retro[0])),
     g_opt_soc_retro,
     (jc_u16)(sizeof(g_opt_soc_retro) / sizeof(g_opt_soc_retro[0])),
     0,
     0,
     (JC_PROFILE_SUBSYS_FS_CPMX | JC_PROFILE_SUBSYS_SHELL_FULL |
      JC_PROFILE_SUBSYS_CACHE | JC_PROFILE_SUBSYS_FASTMEM |
      JC_PROFILE_SUBSYS_DISPLAY | JC_PROFILE_SUBSYS_CAI |
      JC_PROFILE_SUBSYS_FPU | JC_PROFILE_SUBSYS_COMPAT_CPM)},
    {JC_PROFILE_SOC_WORKSTATION,
     0,
     0,
     g_req_soc_workstation,
     (jc_u16)(sizeof(g_req_soc_workstation) /
              sizeof(g_req_soc_workstation[0])),
     g_opt_soc_workstation,
     (jc_u16)(sizeof(g_opt_soc_workstation) /
              sizeof(g_opt_soc_workstation[0])),
     0,
     0,
     (JC_PROFILE_SUBSYS_FS_CPMX | JC_PROFILE_SUBSYS_SHELL_FULL |
      JC_PROFILE_SUBSYS_CACHE | JC_PROFILE_SUBSYS_FASTMEM |
      JC_PROFILE_SUBSYS_DISPLAY | JC_PROFILE_SUBSYS_CAI |
      JC_PROFILE_SUBSYS_FPU | JC_PROFILE_SUBSYS_COMPAT_CPM)}};

const jc_profile_policy *jc_profile_get(jc_u8 profile_id) {
  jc_u32 i;
  for (i = 0; i < (jc_u32)(sizeof(g_profiles) / sizeof(g_profiles[0])); ++i) {
    if (g_profiles[i].profile_id == profile_id) {
      return &g_profiles[i];
    }
  }
  return 0;
}

static int jc_profile_list_contains(const jc_u16 *list,
                                    jc_u16 count,
                                    jc_u16 devclass) {
  jc_u16 i;
  if (!list || count == 0u) {
    return 0;
  }
  for (i = 0; i < count; ++i) {
    if (list[i] == devclass) {
      return 1;
    }
  }
  return 0;
}

int jc_profile_requires_device(const jc_profile_policy *policy,
                               jc_u16 devclass) {
  if (!policy) {
    return 0;
  }
  return jc_profile_list_contains(policy->required_devices,
                                  policy->required_device_count,
                                  devclass);
}

int jc_profile_allows_device(const jc_profile_policy *policy,
                             jc_u16 devclass) {
  if (!policy) {
    return 0;
  }
  if (jc_profile_requires_device(policy, devclass)) {
    return 1;
  }
  return jc_profile_list_contains(policy->optional_devices,
                                  policy->optional_device_count,
                                  devclass);
}

int jc_profile_allows_subsys(const jc_profile_policy *policy,
                             jc_u32 subsys_mask) {
  if (!policy) {
    return 0;
  }
  return (policy->subsys_mask & subsys_mask) == subsys_mask;
}
