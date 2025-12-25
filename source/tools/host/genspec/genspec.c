#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAX_SPECS 64
#define MAX_CONSTS 512
#define MAX_ENUMS 1024
#define MAX_BITS 1024
#define MAX_STRUCTS 256
#define MAX_FIELDS 4096
#define MAX_INPUTS 256

typedef struct {
  char name[64];
  unsigned long major;
  unsigned long minor;
} SpecDef;

typedef struct {
  char name[64];
  unsigned long value;
} ConstDef;

typedef struct {
  char prefix[64];
  char name[64];
  unsigned long value;
} EnumDef;

typedef struct {
  char prefix[64];
  char name[64];
  unsigned long bit;
} BitDef;

typedef struct {
  char name[64];
  unsigned long size;
  unsigned long align;
} StructDef;

typedef struct {
  char struct_name[64];
  char name[64];
  unsigned long offset;
  unsigned long size;
} FieldDef;

typedef struct {
  SpecDef specs[MAX_SPECS];
  size_t spec_count;
  ConstDef consts[MAX_CONSTS];
  size_t const_count;
  EnumDef enums[MAX_ENUMS];
  size_t enum_count;
  BitDef bits[MAX_BITS];
  size_t bit_count;
  StructDef structs[MAX_STRUCTS];
  size_t struct_count;
  FieldDef fields[MAX_FIELDS];
  size_t field_count;
} DefStore;

static void trim(char *s) {
  char *p = s;
  while (*p && isspace((unsigned char)*p)) {
    ++p;
  }
  if (p != s) {
    memmove(s, p, strlen(p) + 1);
  }
  if (*s == '\0') {
    return;
  }
  p = s + strlen(s) - 1;
  while (p >= s && isspace((unsigned char)*p)) {
    *p-- = '\0';
  }
}

static void strip_comment(char *s) {
  char *hash = strchr(s, '#');
  char *slash = strstr(s, "//");
  char *cut = NULL;
  if (hash && slash) {
    cut = (hash < slash) ? hash : slash;
  } else if (hash) {
    cut = hash;
  } else if (slash) {
    cut = slash;
  }
  if (cut) {
    *cut = '\0';
  }
}

static int add_spec(DefStore *store, const char *name, unsigned long major,
                    unsigned long minor) {
  if (store->spec_count >= MAX_SPECS) {
    return 0;
  }
  strncpy(store->specs[store->spec_count].name, name,
          sizeof(store->specs[store->spec_count].name) - 1);
  store->specs[store->spec_count].major = major;
  store->specs[store->spec_count].minor = minor;
  store->spec_count++;
  return 1;
}

static int add_const(DefStore *store, const char *name, unsigned long value) {
  if (store->const_count >= MAX_CONSTS) {
    return 0;
  }
  strncpy(store->consts[store->const_count].name, name,
          sizeof(store->consts[store->const_count].name) - 1);
  store->consts[store->const_count].value = value;
  store->const_count++;
  return 1;
}

static int add_enum(DefStore *store, const char *prefix, const char *name,
                    unsigned long value) {
  if (store->enum_count >= MAX_ENUMS) {
    return 0;
  }
  strncpy(store->enums[store->enum_count].prefix, prefix,
          sizeof(store->enums[store->enum_count].prefix) - 1);
  strncpy(store->enums[store->enum_count].name, name,
          sizeof(store->enums[store->enum_count].name) - 1);
  store->enums[store->enum_count].value = value;
  store->enum_count++;
  return 1;
}

static int add_bit(DefStore *store, const char *prefix, const char *name,
                   unsigned long bit) {
  if (store->bit_count >= MAX_BITS) {
    return 0;
  }
  strncpy(store->bits[store->bit_count].prefix, prefix,
          sizeof(store->bits[store->bit_count].prefix) - 1);
  strncpy(store->bits[store->bit_count].name, name,
          sizeof(store->bits[store->bit_count].name) - 1);
  store->bits[store->bit_count].bit = bit;
  store->bit_count++;
  return 1;
}

static int add_struct(DefStore *store, const char *name, unsigned long size,
                      unsigned long align) {
  if (store->struct_count >= MAX_STRUCTS) {
    return 0;
  }
  strncpy(store->structs[store->struct_count].name, name,
          sizeof(store->structs[store->struct_count].name) - 1);
  store->structs[store->struct_count].size = size;
  store->structs[store->struct_count].align = align;
  store->struct_count++;
  return 1;
}

static int add_field(DefStore *store, const char *struct_name,
                     const char *name, unsigned long offset,
                     unsigned long size) {
  if (store->field_count >= MAX_FIELDS) {
    return 0;
  }
  strncpy(store->fields[store->field_count].struct_name, struct_name,
          sizeof(store->fields[store->field_count].struct_name) - 1);
  strncpy(store->fields[store->field_count].name, name,
          sizeof(store->fields[store->field_count].name) - 1);
  store->fields[store->field_count].offset = offset;
  store->fields[store->field_count].size = size;
  store->field_count++;
  return 1;
}

static int parse_def_file(DefStore *store, const char *path) {
  FILE *fp = fopen(path, "r");
  char line[512];
  if (!fp) {
    fprintf(stderr, "genspec: failed to open %s\n", path);
    return 0;
  }

  while (fgets(line, sizeof(line), fp)) {
    char *token;
    strip_comment(line);
    trim(line);
    if (line[0] == '\0') {
      continue;
    }
    token = strtok(line, " \t\r\n");
    if (!token) {
      continue;
    }

    if (strcmp(token, "SPEC") == 0) {
      char *name = strtok(NULL, " \t\r\n");
      char *major = strtok(NULL, " \t\r\n");
      char *minor = strtok(NULL, " \t\r\n");
      if (!name || !major || !minor) {
        fprintf(stderr, "genspec: bad SPEC line in %s\n", path);
        fclose(fp);
        return 0;
      }
      if (!add_spec(store, name, strtoul(major, NULL, 0),
                    strtoul(minor, NULL, 0))) {
        fprintf(stderr, "genspec: too many specs\n");
        fclose(fp);
        return 0;
      }
    } else if (strcmp(token, "MAGIC") == 0 || strcmp(token, "CONST") == 0) {
      char *name = strtok(NULL, " \t\r\n");
      char *value = strtok(NULL, " \t\r\n");
      if (!name || !value) {
        fprintf(stderr, "genspec: bad CONST/MAGIC line in %s\n", path);
        fclose(fp);
        return 0;
      }
      if (!add_const(store, name, strtoul(value, NULL, 0))) {
        fprintf(stderr, "genspec: too many consts\n");
        fclose(fp);
        return 0;
      }
    } else if (strcmp(token, "ENUM") == 0) {
      char *prefix = strtok(NULL, " \t\r\n");
      char *name = strtok(NULL, " \t\r\n");
      char *value = strtok(NULL, " \t\r\n");
      if (!prefix || !name || !value) {
        fprintf(stderr, "genspec: bad ENUM line in %s\n", path);
        fclose(fp);
        return 0;
      }
      if (!add_enum(store, prefix, name, strtoul(value, NULL, 0))) {
        fprintf(stderr, "genspec: too many enums\n");
        fclose(fp);
        return 0;
      }
    } else if (strcmp(token, "BIT") == 0) {
      char *prefix = strtok(NULL, " \t\r\n");
      char *name = strtok(NULL, " \t\r\n");
      char *bit = strtok(NULL, " \t\r\n");
      if (!prefix || !name || !bit) {
        fprintf(stderr, "genspec: bad BIT line in %s\n", path);
        fclose(fp);
        return 0;
      }
      if (!add_bit(store, prefix, name, strtoul(bit, NULL, 0))) {
        fprintf(stderr, "genspec: too many bits\n");
        fclose(fp);
        return 0;
      }
    } else if (strcmp(token, "STRUCT") == 0) {
      char *name = strtok(NULL, " \t\r\n");
      char *size = strtok(NULL, " \t\r\n");
      char *align = strtok(NULL, " \t\r\n");
      unsigned long align_val = 1;
      if (!name || !size) {
        fprintf(stderr, "genspec: bad STRUCT line in %s\n", path);
        fclose(fp);
        return 0;
      }
      if (align) {
        align_val = strtoul(align, NULL, 0);
      }
      if (!add_struct(store, name, strtoul(size, NULL, 0), align_val)) {
        fprintf(stderr, "genspec: too many structs\n");
        fclose(fp);
        return 0;
      }
    } else if (strcmp(token, "FIELD") == 0) {
      char *struct_name = strtok(NULL, " \t\r\n");
      char *name = strtok(NULL, " \t\r\n");
      char *offset = strtok(NULL, " \t\r\n");
      char *size = strtok(NULL, " \t\r\n");
      if (!struct_name || !name || !offset || !size) {
        fprintf(stderr, "genspec: bad FIELD line in %s\n", path);
        fclose(fp);
        return 0;
      }
      if (!add_field(store, struct_name, name, strtoul(offset, NULL, 0),
                     strtoul(size, NULL, 0))) {
        fprintf(stderr, "genspec: too many fields\n");
        fclose(fp);
        return 0;
      }
    } else {
      fprintf(stderr, "genspec: unknown directive '%s' in %s\n", token, path);
      fclose(fp);
      return 0;
    }
  }
  fclose(fp);
  return 1;
}

static void emit_header_guard(FILE *fp, const char *guard) {
  fprintf(fp, "#ifndef %s\n", guard);
  fprintf(fp, "#define %s\n\n", guard);
}

static void emit_footer_guard(FILE *fp, const char *guard) {
  fprintf(fp, "\n#endif /* %s */\n", guard);
}

static void emit_contracts(const DefStore *store, const char *path) {
  size_t i;
  FILE *fp = fopen(path, "w");
  if (!fp) {
    fprintf(stderr, "genspec: failed to open %s for writing\n", path);
    exit(1);
  }

  fprintf(fp, "/* GENERATED FILE - DO NOT EDIT. */\n");
  emit_header_guard(fp, "JC_CONTRACTS_AUTOGEN_H");

  for (i = 0; i < store->spec_count; ++i) {
    fprintf(fp, "#define JC_SPEC_%s_MAJOR (%luu)\n", store->specs[i].name,
            store->specs[i].major);
    fprintf(fp, "#define JC_SPEC_%s_MINOR (%luu)\n", store->specs[i].name,
            store->specs[i].minor);
  }
  if (store->spec_count) {
    fprintf(fp, "\n");
  }

  for (i = 0; i < store->const_count; ++i) {
    fprintf(fp, "#define JC_%s (0x%lXu)\n", store->consts[i].name,
            store->consts[i].value);
  }
  if (store->const_count) {
    fprintf(fp, "\n");
  }

  for (i = 0; i < store->enum_count; ++i) {
    fprintf(fp, "#define JC_%s_%s (%luu)\n", store->enums[i].prefix,
            store->enums[i].name, store->enums[i].value);
  }
  if (store->enum_count) {
    fprintf(fp, "\n");
  }

  for (i = 0; i < store->bit_count; ++i) {
    fprintf(fp, "#define JC_%s_%s_BIT (%luu)\n", store->bits[i].prefix,
            store->bits[i].name, store->bits[i].bit);
    fprintf(fp, "#define JC_%s_%s_MASK (1u << %luu)\n",
            store->bits[i].prefix, store->bits[i].name, store->bits[i].bit);
  }

  emit_footer_guard(fp, "JC_CONTRACTS_AUTOGEN_H");
  fclose(fp);
}

static void emit_offsets(const DefStore *store, const char *path) {
  size_t i;
  FILE *fp = fopen(path, "w");
  if (!fp) {
    fprintf(stderr, "genspec: failed to open %s for writing\n", path);
    exit(1);
  }

  fprintf(fp, "/* GENERATED FILE - DO NOT EDIT. */\n");
  emit_header_guard(fp, "JC_OFFSETS_AUTOGEN_H");

  for (i = 0; i < store->struct_count; ++i) {
    fprintf(fp, "#define JC_STRUCT_%s_SIZE (%luu)\n",
            store->structs[i].name, store->structs[i].size);
    fprintf(fp, "#define JC_STRUCT_%s_ALIGN (%luu)\n",
            store->structs[i].name, store->structs[i].align);
  }
  if (store->struct_count) {
    fprintf(fp, "\n");
  }

  for (i = 0; i < store->field_count; ++i) {
    fprintf(fp, "#define JC_STRUCT_%s_%s_OFF (%luu)\n",
            store->fields[i].struct_name, store->fields[i].name,
            store->fields[i].offset);
    fprintf(fp, "#define JC_STRUCT_%s_%s_SIZE (%luu)\n",
            store->fields[i].struct_name, store->fields[i].name,
            store->fields[i].size);
  }

  emit_footer_guard(fp, "JC_OFFSETS_AUTOGEN_H");
  fclose(fp);
}

static int is_abs_path(const char *path) {
  if (!path || !path[0]) {
    return 0;
  }
  if ((isalpha((unsigned char)path[0]) && path[1] == ':') || path[0] == '/' ||
      path[0] == '\\') {
    return 1;
  }
  return 0;
}

static void get_base_dir(const char *path, char *out, size_t out_size) {
  const char *last_slash = strrchr(path, '/');
  const char *last_backslash = strrchr(path, '\\');
  const char *cut = last_slash;
  if (!cut || (last_backslash && last_backslash > cut)) {
    cut = last_backslash;
  }
  if (!cut) {
    out[0] = '\0';
    return;
  }
  {
    size_t len = (size_t)(cut - path + 1);
    if (len >= out_size) {
      len = out_size - 1;
    }
    memcpy(out, path, len);
    out[len] = '\0';
  }
}

static void join_path(char *out, size_t out_size, const char *base,
                      const char *rel) {
  if (!base || base[0] == '\0') {
    strncpy(out, rel, out_size - 1);
    out[out_size - 1] = '\0';
    return;
  }
  strncpy(out, base, out_size - 1);
  out[out_size - 1] = '\0';
  if (strlen(out) + strlen(rel) + 1 < out_size) {
    strcat(out, rel);
  }
}

static int read_list_file(const char *list_path, char paths[][260],
                          size_t *count) {
  FILE *fp = fopen(list_path, "r");
  char line[260];
  char base_dir[260];
  if (!fp) {
    fprintf(stderr, "genspec: failed to open list %s\n", list_path);
    return 0;
  }
  get_base_dir(list_path, base_dir, sizeof(base_dir));
  while (fgets(line, sizeof(line), fp)) {
    strip_comment(line);
    trim(line);
    if (line[0] == '\0') {
      continue;
    }
    if (*count >= MAX_INPUTS) {
      fclose(fp);
      fprintf(stderr, "genspec: too many input files\n");
      return 0;
    }
    if (is_abs_path(line)) {
      strncpy(paths[*count], line, sizeof(paths[*count]) - 1);
      paths[*count][sizeof(paths[*count]) - 1] = '\0';
    } else {
      join_path(paths[*count], sizeof(paths[*count]), base_dir, line);
    }
    (*count)++;
  }
  fclose(fp);
  return 1;
}

static void usage(void) {
  fprintf(stderr,
          "usage: genspec --list <defs.lst> --out-dir <dir> [def...]\n");
}

int main(int argc, char **argv) {
  DefStore store;
  char input_paths[MAX_INPUTS][260];
  size_t input_count = 0;
  const char *list_path = NULL;
  const char *out_dir = NULL;
  char contracts_path[260];
  char offsets_path[260];
  int i;

  memset(&store, 0, sizeof(store));

  for (i = 1; i < argc; ++i) {
    if (strcmp(argv[i], "--list") == 0 && i + 1 < argc) {
      list_path = argv[++i];
    } else if (strcmp(argv[i], "--out-dir") == 0 && i + 1 < argc) {
      out_dir = argv[++i];
    } else if (argv[i][0] == '-') {
      usage();
      return 1;
    } else {
      if (input_count >= MAX_INPUTS) {
        fprintf(stderr, "genspec: too many input files\n");
        return 1;
      }
      strncpy(input_paths[input_count], argv[i],
              sizeof(input_paths[input_count]) - 1);
      input_paths[input_count][sizeof(input_paths[input_count]) - 1] = '\0';
      input_count++;
    }
  }

  if (!out_dir || !list_path) {
    usage();
    return 1;
  }

  if (!read_list_file(list_path, input_paths, &input_count)) {
    return 1;
  }

  for (i = 0; i < (int)input_count; ++i) {
    if (!parse_def_file(&store, input_paths[i])) {
      return 1;
    }
  }

  sprintf(contracts_path, "%s/jc_contracts_autogen.h", out_dir);
  sprintf(offsets_path, "%s/jc_offsets_autogen.h", out_dir);

  emit_contracts(&store, contracts_path);
  emit_offsets(&store, offsets_path);
  return 0;
}
