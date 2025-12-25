#ifndef JC_DOS_SHELL_CMDS_H
#define JC_DOS_SHELL_CMDS_H

void jc_shell_cmd_dir(const char *pattern);
void jc_shell_cmd_type(const char *name);
void jc_shell_cmd_copy(const char *src, const char *dst);
void jc_shell_cmd_del(const char *name);
void jc_shell_cmd_ren(const char *old_name, const char *new_name);
void jc_shell_cmd_run(const char *opt, const char *name);

#endif /* JC_DOS_SHELL_CMDS_H */
