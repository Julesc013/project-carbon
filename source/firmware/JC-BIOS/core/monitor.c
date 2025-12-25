#include "jc_monitor.h"

#include "jc_bdt.h"
#include "jc_bios.h"
#include "jc_block.h"
#include "jc_console.h"
#include "jc_contracts_autogen.h"
#include "jc_offsets_autogen.h"
#include "jc_mode.h"
#include "jc_timer.h"
#include "jc_util.h"
#include "fs_cpmx.h"
#include "loader_jcom.h"

#define JC_MONITOR_LINE_MAX 80u
#define JC_MONITOR_DUMP_MAX 256u

static void jc_console_write_hex32(jc_u32 value) {
  char buf[8];
  jc_u32_to_hex(buf, value);
  jc_console_putc(buf[0]);
  jc_console_putc(buf[1]);
  jc_console_putc(buf[2]);
  jc_console_putc(buf[3]);
  jc_console_putc(buf[4]);
  jc_console_putc(buf[5]);
  jc_console_putc(buf[6]);
  jc_console_putc(buf[7]);
}

static void jc_console_write_hex16(jc_u16 value) {
  char buf[4];
  jc_u16_to_hex(buf, value);
  jc_console_putc(buf[0]);
  jc_console_putc(buf[1]);
  jc_console_putc(buf[2]);
  jc_console_putc(buf[3]);
}

static void jc_console_write_hex64(jc_u64 value) {
  jc_console_write_hex32(value.hi);
  jc_console_write_hex32(value.lo);
}

static void jc_monitor_prompt(void) {
  jc_console_write("JC> ");
}

static void jc_monitor_help(void) {
  jc_console_write("HELP\r\n");
  jc_console_write("STATE\r\n");
  jc_console_write("CAPS\r\n");
  jc_console_write("BDT\r\n");
  jc_console_write("DISKINFO\r\n");
  jc_console_write("DISKTEST\r\n");
  jc_console_write("LS\r\n");
  jc_console_write("TYPE <file>\r\n");
  jc_console_write("COPY <src> <dst>\r\n");
  jc_console_write("DEL <file>\r\n");
  jc_console_write("REN <old> <new>\r\n");
  jc_console_write("LOAD <file>\r\n");
  jc_console_write("RUN <file>\r\n");
  jc_console_write("MD <addr> <len>\r\n");
  jc_console_write("MW <addr> <val> (use MW! to override MMIO)\r\n");
  jc_console_write("REGS\r\n");
  jc_console_write("MODETEST\r\n");
  jc_console_write("REBOOT\r\n");
}

static void jc_monitor_state(void) {
  jc_console_write("PHASE ");
  jc_console_write(jc_boot_phase_name(jc_boot_get_phase()));
  jc_console_write(" LAST_ERROR ");
  jc_console_write(jc_error_name(jc_boot_get_error()));
  jc_console_write(" (0x");
  jc_console_write_hex16(jc_boot_get_error());
  jc_console_write(")\r\n");
}

static void jc_monitor_caps(void) {
  const jc_capset_v1 *capset = jc_boot_capset();
  if (!capset) {
    jc_console_write("CAPSET unavailable\r\n");
    return;
  }
  jc_console_write("CAPSET signature=0x");
  jc_console_write_hex32(capset->signature);
  jc_console_write(" version=");
  jc_console_write_hex16(capset->version);
  jc_console_write(" size=");
  jc_console_write_hex16(capset->size_bytes);
  jc_console_write("\r\n");

  jc_console_write("CPU ladder=");
  jc_console_write_hex16(capset->cpu_ladder_id);
  jc_console_write(" tier=");
  jc_console_write_hex16(capset->presented_cpu_tier);
  jc_console_write(" FPU ladder=");
  jc_console_write_hex16(capset->fpu_ladder_id);
  jc_console_write(" tier=");
  jc_console_write_hex16(capset->presented_fpu_tier);
  jc_console_write(" profile=");
  jc_console_write_hex16(capset->profile_id);
  jc_console_write("\r\n");

  jc_console_write("CPU features ");
  jc_console_write_hex32(capset->cpu_features[0]);
  jc_console_write(" ");
  jc_console_write_hex32(capset->cpu_features[1]);
  jc_console_write(" ");
  jc_console_write_hex32(capset->cpu_features[2]);
  jc_console_write(" ");
  jc_console_write_hex32(capset->cpu_features[3]);
  jc_console_write("\r\n");

  jc_console_write("FPU features ");
  jc_console_write_hex32(capset->fpu_features[0]);
  jc_console_write(" ");
  jc_console_write_hex32(capset->fpu_features[1]);
  jc_console_write(" ");
  jc_console_write_hex32(capset->fpu_features[2]);
  jc_console_write(" ");
  jc_console_write_hex32(capset->fpu_features[3]);
  jc_console_write("\r\n");

  jc_console_write("PERIPH features ");
  jc_console_write_hex32(capset->periph_features[0]);
  jc_console_write(" ");
  jc_console_write_hex32(capset->periph_features[1]);
  jc_console_write(" ");
  jc_console_write_hex32(capset->periph_features[2]);
  jc_console_write(" ");
  jc_console_write_hex32(capset->periph_features[3]);
  jc_console_write("\r\n");

  jc_console_write("TOPOLOGY 0x");
  jc_console_write_hex64(capset->topology_table_ptr);
  jc_console_write("\r\nBDT 0x");
  jc_console_write_hex64(capset->bdt_ptr);
  jc_console_write("\r\nLIMITS 0x");
  jc_console_write_hex64(capset->limits_table_ptr);
  jc_console_write("\r\nMEMREG 0x");
  jc_console_write_hex64(capset->mem_region_table_ptr);
  jc_console_write("\r\nTIERHOST 0x");
  jc_console_write_hex64(capset->tier_host_table_ptr);
  jc_console_write("\r\n");

  jc_console_write("MAX_DEV ");
  jc_console_write_hex16(capset->max_devices);
  jc_console_write(" MAX_BDT ");
  jc_console_write_hex16(capset->max_bdt_entries);
  jc_console_write(" MAX_IRQ ");
  jc_console_write_hex16(capset->max_irq_routes);
  jc_console_write(" MAX_DMA ");
  jc_console_write_hex16(capset->max_dma_segments);
  jc_console_write("\r\n");
}

static void jc_monitor_bdt(void) {
  const jc_bdt_index *bdt = jc_boot_bdt_index();
  jc_u16 i;
  if (!bdt || !bdt->header) {
    jc_console_write("BDT unavailable\r\n");
    return;
  }
  jc_console_write("BDT signature=0x");
  jc_console_write_hex32(bdt->header->signature);
  jc_console_write(" version=");
  jc_console_write_hex16(bdt->header->header_version);
  jc_console_write(" entries=");
  jc_console_write_hex16(bdt->header->entry_count);
  jc_console_write(" total=0x");
  jc_console_write_hex32(bdt->header->total_size);
  jc_console_write("\r\n");

  for (i = 0; i < bdt->entry_count; ++i) {
    const jc_bdt_entry_v1 *entry = bdt->index[i].entry;
    jc_console_write("ENTRY ");
    jc_console_write_hex16((jc_u16)i);
    jc_console_write(" class=");
    jc_console_write_hex16(entry->class_id);
    jc_console_write(" inst=");
    jc_console_write_hex16(entry->instance_id);
    jc_console_write(" mmio=0x");
    jc_console_write_hex64(entry->mmio_base);
    jc_console_write(" size=0x");
    jc_console_write_hex32(entry->mmio_size);
    jc_console_write(" io=0x");
    jc_console_write_hex32(entry->io_port_base);
    jc_console_write(" iosz=0x");
    jc_console_write_hex16(entry->io_port_size);
    jc_console_write(" caps0=0x");
    jc_console_write_hex32(entry->caps0);
    jc_console_write(" caps1=0x");
    jc_console_write_hex32(entry->caps1);
    jc_console_write("\r\n");
  }
}

static void jc_monitor_print_name(const jc_u8 name[8], const jc_u8 ext[3]) {
  int i;
  int end = 7;
  int ext_end = 2;
  while (end >= 0 && name[end] == 0x20) {
    end--;
  }
  for (i = 0; i <= end; ++i) {
    jc_console_putc((char)name[i]);
  }
  while (ext_end >= 0 && ext[ext_end] == 0x20) {
    ext_end--;
  }
  if (ext_end >= 0) {
    jc_console_putc('.');
    for (i = 0; i <= ext_end; ++i) {
      jc_console_putc((char)ext[i]);
    }
  }
}

static void jc_monitor_ls_cb(const jc_fs_file_info *info, void *ctx) {
  (void)ctx;
  jc_console_write("FILE ");
  jc_monitor_print_name(info->name, info->ext);
  jc_console_write(" SIZE ");
  jc_console_write_hex32(info->size_bytes);
  jc_console_write("\r\n");
}

static void jc_monitor_diskinfo(void) {
  jc_block_params params;
  jc_error_t err = jc_blk_open(0);
  if (err != JC_E_OK) {
    jc_console_write("DISKINFO FAIL ");
    jc_console_write_hex16(err);
    jc_console_write("\r\n");
    return;
  }
  err = jc_blk_get_params(&params);
  if (err != JC_E_OK) {
    jc_console_write("DISKINFO FAIL ");
    jc_console_write_hex16(err);
    jc_console_write("\r\n");
    return;
  }
  jc_console_write("DISKINFO BLOCK_SIZE ");
  jc_console_write_hex32(params.block_size_bytes);
  jc_console_write(" MAX_SECT ");
  jc_console_write_hex32(params.max_sectors_per_op);
  jc_console_write(" TOTAL_SECT ");
  jc_console_write_hex32(params.total_sectors);
  jc_console_write(" TIMEOUT ");
  jc_console_write_hex32(params.timeout_ticks);
  jc_console_write("\r\n");
}

static void jc_monitor_disktest(void) {
  jc_error_t err = jc_blk_self_test();
  if (err == JC_E_OK) {
    jc_console_write("DISKTEST PASS\r\n");
  } else {
    jc_console_write("DISKTEST FAIL ");
    jc_console_write_hex16(err);
    jc_console_write("\r\n");
  }
}

static void jc_monitor_ls(void) {
  jc_error_t err = jc_fs_list(jc_monitor_ls_cb, 0);
  if (err != JC_E_OK) {
    jc_console_write("LS FAIL ");
    jc_console_write_hex16(err);
    jc_console_write("\r\n");
  }
}

static void jc_monitor_type(const char *name) {
  jc_fs_handle handle;
  jc_u8 buf[64];
  jc_error_t err = jc_fs_open(&handle, name, JC_FS_MODE_READ);
  if (err != JC_E_OK) {
    jc_console_write("TYPE FAIL ");
    jc_console_write_hex16(err);
    jc_console_write("\r\n");
    return;
  }
  for (;;) {
    jc_u32 got = 0;
    err = jc_fs_read(&handle, buf, sizeof(buf), &got);
    if (err != JC_E_OK) {
      jc_console_write("TYPE FAIL ");
      jc_console_write_hex16(err);
      jc_console_write("\r\n");
      return;
    }
    if (got == 0) {
      break;
    }
    {
      jc_u32 i;
      for (i = 0; i < got; ++i) {
        if (buf[i] == '\n') {
          jc_console_putc('\r');
        }
        jc_console_putc((char)buf[i]);
      }
    }
  }
  jc_console_write("\r\n");
  jc_fs_close(&handle);
}

static void jc_monitor_copy(const char *src, const char *dst) {
  jc_fs_handle in_handle;
  jc_fs_handle out_handle;
  jc_u8 buf[128];
  jc_error_t err = jc_fs_open(&in_handle, src, JC_FS_MODE_READ);
  if (err != JC_E_OK) {
    jc_console_write("COPY FAIL ");
    jc_console_write_hex16(err);
    jc_console_write("\r\n");
    return;
  }
  err = jc_fs_open(&out_handle, dst,
                   JC_FS_MODE_WRITE | JC_FS_MODE_CREATE | JC_FS_MODE_TRUNC);
  if (err != JC_E_OK) {
    jc_console_write("COPY FAIL ");
    jc_console_write_hex16(err);
    jc_console_write("\r\n");
    return;
  }
  for (;;) {
    jc_u32 got = 0;
    jc_u32 wrote = 0;
    err = jc_fs_read(&in_handle, buf, sizeof(buf), &got);
    if (err != JC_E_OK) {
      jc_console_write("COPY FAIL ");
      jc_console_write_hex16(err);
      jc_console_write("\r\n");
      return;
    }
    if (got == 0) {
      break;
    }
    err = jc_fs_write(&out_handle, buf, got, &wrote);
    if (err != JC_E_OK || wrote != got) {
      jc_console_write("COPY FAIL ");
      jc_console_write_hex16(err);
      jc_console_write("\r\n");
      return;
    }
  }
  jc_fs_close(&out_handle);
  jc_fs_close(&in_handle);
  jc_console_write("COPY OK\r\n");
}

static void jc_monitor_del(const char *name) {
  jc_error_t err = jc_fs_delete(name);
  if (err == JC_E_OK) {
    jc_console_write("DEL OK\r\n");
  } else {
    jc_console_write("DEL FAIL ");
    jc_console_write_hex16(err);
    jc_console_write("\r\n");
  }
}

static void jc_monitor_ren(const char *old_name, const char *new_name) {
  jc_error_t err = jc_fs_rename(old_name, new_name);
  if (err == JC_E_OK) {
    jc_console_write("REN OK\r\n");
  } else {
    jc_console_write("REN FAIL ");
    jc_console_write_hex16(err);
    jc_console_write("\r\n");
  }
}

static void jc_monitor_load(const char *name) {
  jc_jcom_image image;
  jc_error_t err = jc_jcom_load(name, &image);
  if (err == JC_E_OK) {
    jc_console_write("LOAD OK ENTRY ");
    jc_console_write_hex32(image.entry_addr);
    jc_console_write("\r\n");
  } else {
    jc_console_write("LOAD FAIL ");
    jc_console_write_hex16(err);
    jc_console_write("\r\n");
  }
}

static void jc_monitor_run_jcom(const char *name) {
  jc_u8 rc = 0;
  jc_error_t err = jc_jcom_run(name, &rc);
  if (err == JC_E_OK) {
    jc_console_write("RUN OK RC ");
    jc_console_write_hex16(rc);
    jc_console_write("\r\n");
  } else {
    jc_console_write("RUN FAIL ");
    jc_console_write_hex16(err);
    jc_console_write("\r\n");
  }
}

static int jc_monitor_is_mmio_addr(jc_u32 addr) {
  const jc_bdt_index *bdt = jc_boot_bdt_index();
  jc_u16 i;
  if (!bdt) {
    return 0;
  }
  for (i = 0; i < bdt->entry_count; ++i) {
    const jc_bdt_entry_v1 *entry = bdt->index[i].entry;
    if (entry && entry->mmio_size != 0u) {
      const jc_u32 base = entry->mmio_base.lo;
      const jc_u32 end = base + entry->mmio_size - 1u;
      if (addr >= base && addr <= end) {
        return 1;
      }
    }
  }
  return 0;
}

static void jc_monitor_md(jc_u32 addr, jc_u32 len) {
  jc_u32 i;
  if (len > JC_MONITOR_DUMP_MAX) {
    len = JC_MONITOR_DUMP_MAX;
  }
  for (i = 0; i < len; ++i) {
    jc_u32 cur = addr + i;
    jc_u8 value = *(volatile jc_u8 *)(unsigned long)cur;
    if ((i % 16u) == 0u) {
      jc_console_write("\r\n");
      jc_console_write_hex16((jc_u16)cur);
      jc_console_write(": ");
    }
    jc_console_write_hex16((jc_u16)value);
    jc_console_putc(' ');
  }
  jc_console_write("\r\n");
}

static void jc_monitor_mw(jc_u32 addr, jc_u32 value, int override_mmio) {
  if (jc_monitor_is_mmio_addr(addr) && !override_mmio) {
    jc_console_write("MW refused: MMIO address\r\n");
    return;
  }
  *(volatile jc_u8 *)(unsigned long)addr = (jc_u8)value;
  jc_console_write("MW OK\r\n");
}

static void jc_monitor_regs(void) {
  jc_u16 sp_snapshot;
  jc_console_write("AF=0000 BC=0000 DE=0000 HL=0000 ");
  sp_snapshot = (jc_u16)(unsigned long)&sp_snapshot;
  jc_console_write("SP=");
  jc_console_write_hex16(sp_snapshot);
  jc_console_write(" TIER=");
  jc_console_write_hex16(jc_mode_current_tier());
  jc_console_write("\r\n");
}

static int g_mode_test_returned = 0;

static void jc_mode_test_entry(void) {
  g_mode_test_returned = 1;
  jc_retmd_request();
}

static void jc_monitor_modetest(void) {
  const jc_capset_v1 *capset = jc_boot_capset();
  jc_u8 start = jc_mode_current_tier();
  jc_u8 max = capset ? capset->presented_cpu_tier : start;
  jc_u8 tier;

  jc_console_write("MODETEST\r\n");
  for (tier = (jc_u8)(start + 1u); tier <= max; ++tier) {
    jc_mode_abi_v1 capsule;
    jc_error_t err;
    g_mode_test_returned = 0;
    jc_memset(&capsule, 0, sizeof(capsule));
    capsule.version = JC_MODE_ABI_V1_VERSION;
    capsule.size_bytes = JC_STRUCT_MODE_ABI_V1_SIZE;
    capsule.target_tier = tier;
    capsule.entry_vector = jc_u64_make((jc_u32)(unsigned long)&jc_mode_test_entry, 0);
    err = jc_modeup_request(&capsule);
    jc_console_write("TEST MODE_P");
    jc_console_putc((char)('0' + tier));
    if (err == JC_E_OK && g_mode_test_returned &&
        jc_mode_current_tier() == start) {
      jc_console_write(" PASS\r\n");
    } else {
      jc_console_write(" FAIL ");
      jc_console_write_hex16(err);
      jc_console_write("\r\n");
    }
  }
}

static void jc_monitor_reboot(void) {
  void (*reset)(void) = (void (*)(void))0x0000;
  jc_console_write("REBOOT\r\n");
  reset();
}

static jc_u32 jc_split_tokens(char *line, char *argv[], jc_u32 max_args) {
  jc_u32 argc = 0;
  jc_u32 i = 0;
  while (line[i] != '\0') {
    while (jc_is_space(line[i])) {
      line[i] = '\0';
      i++;
    }
    if (line[i] == '\0') {
      break;
    }
    if (argc < max_args) {
      argv[argc++] = &line[i];
    }
    while (line[i] != '\0' && !jc_is_space(line[i])) {
      i++;
    }
  }
  return argc;
}

void jc_monitor_run(void) {
  char line[JC_MONITOR_LINE_MAX];
  char *argv[4];

  for (;;) {
    jc_monitor_prompt();
    if (jc_console_readline(line, sizeof(line)) != JC_E_OK) {
      continue;
    }
    if (line[0] == '\0') {
      continue;
    }
    {
      jc_u32 argc = jc_split_tokens(line, argv, 4);
      int override_mmio = 0;
      if (argc == 0) {
        continue;
      }
      if (jc_strcasecmp(argv[0], "HELP") == 0) {
        jc_monitor_help();
      } else if (jc_strcasecmp(argv[0], "STATE") == 0) {
        jc_monitor_state();
      } else if (jc_strcasecmp(argv[0], "CAPS") == 0) {
        jc_monitor_caps();
      } else if (jc_strcasecmp(argv[0], "BDT") == 0) {
        jc_monitor_bdt();
      } else if (jc_strcasecmp(argv[0], "DISKINFO") == 0) {
        jc_monitor_diskinfo();
      } else if (jc_strcasecmp(argv[0], "DISKTEST") == 0) {
        jc_monitor_disktest();
      } else if (jc_strcasecmp(argv[0], "LS") == 0) {
        jc_monitor_ls();
      } else if (jc_strcasecmp(argv[0], "TYPE") == 0 && argc >= 2) {
        jc_monitor_type(argv[1]);
      } else if (jc_strcasecmp(argv[0], "COPY") == 0 && argc >= 3) {
        jc_monitor_copy(argv[1], argv[2]);
      } else if (jc_strcasecmp(argv[0], "DEL") == 0 && argc >= 2) {
        jc_monitor_del(argv[1]);
      } else if (jc_strcasecmp(argv[0], "REN") == 0 && argc >= 3) {
        jc_monitor_ren(argv[1], argv[2]);
      } else if (jc_strcasecmp(argv[0], "LOAD") == 0 && argc >= 2) {
        jc_monitor_load(argv[1]);
      } else if (jc_strcasecmp(argv[0], "RUN") == 0 && argc >= 2) {
        jc_monitor_run_jcom(argv[1]);
      } else if (jc_strcasecmp(argv[0], "MD") == 0 && argc >= 3) {
        jc_u32 addr;
        jc_u32 len;
        if (jc_parse_u32(argv[1], &addr) && jc_parse_u32(argv[2], &len)) {
          jc_monitor_md(addr, len);
        } else {
          jc_console_write("MD parse error\r\n");
        }
      } else if ((jc_strcasecmp(argv[0], "MW") == 0 ||
                  jc_strcasecmp(argv[0], "MW!") == 0) &&
                 argc >= 3) {
        jc_u32 addr;
        jc_u32 val;
        if (jc_strcasecmp(argv[0], "MW!") == 0) {
          override_mmio = 1;
        }
        if (jc_parse_u32(argv[1], &addr) && jc_parse_u32(argv[2], &val)) {
          jc_monitor_mw(addr, val, override_mmio);
        } else {
          jc_console_write("MW parse error\r\n");
        }
      } else if (jc_strcasecmp(argv[0], "REGS") == 0) {
        jc_monitor_regs();
      } else if (jc_strcasecmp(argv[0], "MODETEST") == 0) {
        jc_monitor_modetest();
      } else if (jc_strcasecmp(argv[0], "REBOOT") == 0) {
        jc_monitor_reboot();
      } else {
        jc_console_write("Unknown command\r\n");
      }
    }
  }
}
