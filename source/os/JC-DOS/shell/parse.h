#ifndef JC_DOS_SHELL_PARSE_H
#define JC_DOS_SHELL_PARSE_H

#include "jc_types.h"

jc_u32 jc_shell_split_tokens(char *line, char *argv[], jc_u32 max_args);

#endif /* JC_DOS_SHELL_PARSE_H */
