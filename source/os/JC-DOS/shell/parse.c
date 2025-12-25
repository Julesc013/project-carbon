#include "parse.h"

#include "jc_dos_util.h"

jc_u32 jc_shell_split_tokens(char *line, char *argv[], jc_u32 max_args) {
  jc_u32 argc = 0;
  jc_u32 i = 0;
  while (line[i] != '\0') {
    while (jc_dos_is_space(line[i])) {
      line[i] = '\0';
      i++;
    }
    if (line[i] == '\0') {
      break;
    }
    if (argc < max_args) {
      argv[argc++] = &line[i];
    }
    while (line[i] != '\0' && !jc_dos_is_space(line[i])) {
      i++;
    }
  }
  return argc;
}
