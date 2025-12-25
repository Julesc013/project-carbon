#include "shell.h"

#include "bios_services.h"
#include "handoff.h"
#include "jc_config.h"
#include "jc_dos_util.h"
#include "jc_profile.h"
#include "log.h"
#include "parse.h"
#include "shell_cmds.h"

#define JC_SHELL_LINE_MAX 80u

static int jc_shell_full_allowed(void) {
  const jc_profile_policy *policy = jc_dos_profile_policy();
  if (JC_CFG_SHELL_MINIMAL != 0) {
    return 0;
  }
  if (!policy) {
    return 1;
  }
  return jc_profile_allows_subsys(policy, JC_PROFILE_SUBSYS_SHELL_FULL);
}

static int jc_shell_command_allowed(const char *cmd) {
  if (jc_shell_full_allowed()) {
    return 1;
  }
  if (!cmd) {
    return 0;
  }
  if (jc_dos_strcasecmp(cmd, "DIR") == 0) {
    return 1;
  }
  if (jc_dos_strcasecmp(cmd, "TYPE") == 0) {
    return 1;
  }
  if (jc_dos_strcasecmp(cmd, "RUN") == 0) {
    return 1;
  }
  return 0;
}

void jc_shell_run(void) {
  char line[JC_SHELL_LINE_MAX];
  char *argv[4];

  for (;;) {
    jc_dos_log("JC-DOS> ");
    if (jc_bios_console_readline(line, sizeof(line)) != JC_E_OK) {
      continue;
    }
    if (line[0] == '\0') {
      continue;
    }
    {
      jc_u32 argc = jc_shell_split_tokens(line, argv, 4);
      if (argc == 0) {
        continue;
      }
      if (!jc_shell_command_allowed(argv[0])) {
        jc_dos_log("CMD DISABLED\r\n");
        continue;
      }
      if (jc_dos_strcasecmp(argv[0], "DIR") == 0) {
        jc_shell_cmd_dir(argc >= 2 ? argv[1] : 0);
      } else if (jc_dos_strcasecmp(argv[0], "TYPE") == 0 && argc >= 2) {
        jc_shell_cmd_type(argv[1]);
      } else if (jc_dos_strcasecmp(argv[0], "COPY") == 0 && argc >= 3) {
        jc_shell_cmd_copy(argv[1], argv[2]);
      } else if (jc_dos_strcasecmp(argv[0], "DEL") == 0 && argc >= 2) {
        jc_shell_cmd_del(argv[1]);
      } else if (jc_dos_strcasecmp(argv[0], "REN") == 0 && argc >= 3) {
        jc_shell_cmd_ren(argv[1], argv[2]);
      } else if (jc_dos_strcasecmp(argv[0], "RUN") == 0 && argc >= 2) {
        if (argc >= 3 && argv[1][0] == '/') {
          jc_shell_cmd_run(argv[1], argv[2]);
        } else {
          jc_shell_cmd_run(0, argv[1]);
        }
      } else {
        jc_dos_log("Unknown command\r\n");
      }
    }
  }
}
