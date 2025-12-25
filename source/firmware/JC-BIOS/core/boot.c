#include "jc_bios.h"

#include "jc_bdt.h"
#include "jc_capset.h"
#include "jc_console.h"
#include "jc_conformance.h"
#include "jc_contracts_autogen.h"
#include "jc_discovery.h"
#include "jc_monitor.h"
#include "jc_mode.h"
#include "jc_timer.h"
#include "jc_util.h"

typedef struct {
  jc_boot_phase_t phase;
  jc_error_t last_error;
  const jc_bsp_anchor_v1 *anchor;
  const jc_discovery_table_v1 *discovery;
  jc_bdt_index bdt_index;
  jc_capset_v1 capset;
  jc_u32 capset_crc32;
} jc_bios_context;

static jc_bios_context g_ctx;

static void jc_boot_record_error(jc_boot_phase_t phase, jc_error_t err) {
  g_ctx.phase = phase;
  if (err != JC_E_OK) {
    g_ctx.last_error = err;
  }
}

void jc_boot_set_phase(jc_boot_phase_t phase) {
  g_ctx.phase = phase;
}

jc_boot_phase_t jc_boot_get_phase(void) {
  return g_ctx.phase;
}

void jc_boot_set_error(jc_error_t err) {
  if (err != JC_E_OK) {
    g_ctx.last_error = err;
  }
}

jc_error_t jc_boot_get_error(void) {
  return g_ctx.last_error;
}

const char *jc_boot_phase_name(jc_boot_phase_t phase) {
  switch (phase) {
    case JC_BOOT_PHASE_RESET:
      return "RESET";
    case JC_BOOT_PHASE_DISCOVERY:
      return "DISCOVERY";
    case JC_BOOT_PHASE_BDT:
      return "BDT";
    case JC_BOOT_PHASE_TIMER:
      return "TIMER";
    case JC_BOOT_PHASE_CONSOLE:
      return "CONSOLE";
    case JC_BOOT_PHASE_CAPSET:
      return "CAPSET";
    case JC_BOOT_PHASE_MONITOR:
      return "MONITOR";
    case JC_BOOT_PHASE_MODE:
      return "MODE";
    default:
      return "UNKNOWN";
  }
}

const char *jc_error_name(jc_error_t err) {
  switch (err) {
    case JC_E_OK:
      return "OK";
    case JC_E_BOOT_BSP_MISSING:
      return "BOOT_BSP_MISSING";
    case JC_E_BOOT_BSP_BAD_SIGNATURE:
      return "BOOT_BSP_BAD_SIGNATURE";
    case JC_E_BOOT_DISCOVERY_MISSING:
      return "BOOT_DISCOVERY_MISSING";
    case JC_E_BOOT_UNSUPPORTED_PROFILE:
      return "BOOT_UNSUPPORTED_PROFILE";
    case JC_E_DISCOVERY_BAD_SIGNATURE:
      return "DISCOVERY_BAD_SIGNATURE";
    case JC_E_DISCOVERY_BAD_VERSION:
      return "DISCOVERY_BAD_VERSION";
    case JC_E_DISCOVERY_BAD_SIZE:
      return "DISCOVERY_BAD_SIZE";
    case JC_E_DISCOVERY_BAD_POINTER:
      return "DISCOVERY_BAD_POINTER";
    case JC_E_BDT_BAD_SIGNATURE:
      return "BDT_BAD_SIGNATURE";
    case JC_E_BDT_BAD_VERSION:
      return "BDT_BAD_VERSION";
    case JC_E_BDT_BAD_SIZE:
      return "BDT_BAD_SIZE";
    case JC_E_BDT_BAD_CHECKSUM:
      return "BDT_BAD_CHECKSUM";
    case JC_E_DEV_NOT_FOUND:
      return "DEV_NOT_FOUND";
    case JC_E_DEV_UNSUPPORTED:
      return "DEV_UNSUPPORTED";
    case JC_E_DEV_IO_TIMEOUT:
      return "DEV_IO_TIMEOUT";
    case JC_E_DEV_IO_ERROR:
      return "DEV_IO_ERROR";
    case JC_E_FS_BAD_SUPER:
      return "FS_BAD_SUPER";
    case JC_E_FS_BAD_DIR:
      return "FS_BAD_DIR";
    case JC_E_FS_NO_SPACE:
      return "FS_NO_SPACE";
    case JC_E_FS_NOT_FOUND:
      return "FS_NOT_FOUND";
    case JC_E_EXEC_BAD_MAGIC:
      return "EXEC_BAD_MAGIC";
    case JC_E_EXEC_BAD_VERSION:
      return "EXEC_BAD_VERSION";
    case JC_E_EXEC_BAD_CRC:
      return "EXEC_BAD_CRC";
    case JC_E_EXEC_UNSUPPORTED_TIER:
      return "EXEC_UNSUPPORTED_TIER";
    case JC_E_MODE_INVALID_TARGET:
      return "MODE_INVALID_TARGET";
    case JC_E_MODE_NOT_PERMITTED:
      return "MODE_NOT_PERMITTED";
    case JC_E_MODE_STACK_OVERFLOW:
      return "MODE_STACK_OVERFLOW";
    case JC_E_MODE_STACK_UNDERFLOW:
      return "MODE_STACK_UNDERFLOW";
    case JC_E_INTERNAL_ASSERT:
      return "INTERNAL_ASSERT";
    case JC_E_INTERNAL_UNREACHABLE:
      return "INTERNAL_UNREACHABLE";
    default:
      return "UNKNOWN";
  }
}

const jc_bdt_index *jc_boot_bdt_index(void) {
  return &g_ctx.bdt_index;
}

const jc_capset_v1 *jc_boot_capset(void) {
  return &g_ctx.capset;
}

jc_u32 jc_boot_capset_crc32(void) {
  return g_ctx.capset_crc32;
}

jc_u32 jc_boot_bdt_crc32(void) {
  return g_ctx.bdt_index.crc32;
}

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

static void jc_boot_print_header(void) {
  jc_console_write("JC-BIOS BOOT v0.3\r\n");
  jc_console_write(
      "CONTRACTS SPEC_TIERS=1.0 SPEC_PROFILES=1.0 SPEC_MODE=1.0 "
      "SPEC_DISCOVERY=1.0 SPEC_CAPSET=1.0 SPEC_TOPOLOGY=1.0 SPEC_BDT=1.0 "
      "SPEC_IRQ=1.0 SPEC_DEV_UART=1.0 SPEC_DEV_TIMER=1.0 SPEC_DEV_PIC=1.0 "
      "SPEC_DEV_STORAGE_IDEPIO=1.0 SPEC_CAI=1.0 SPEC_JCOM=1.0 "
      "SPEC_FS_CPMX=1.0 SPEC_CONFORMANCE=1.0\r\n");
  jc_console_write("CAPSET_CRC32 ");
  jc_console_write_hex32(g_ctx.capset_crc32);
  jc_console_write("\r\n");
  jc_console_write("BDT_CRC32 ");
  jc_console_write_hex32(g_ctx.bdt_index.crc32);
  jc_console_write("\r\n");
}

void jc_bios_p0_entry(void) {
  jc_error_t err;

  jc_memset(&g_ctx, 0, sizeof(g_ctx));
  g_ctx.phase = JC_BOOT_PHASE_RESET;
  g_ctx.last_error = JC_E_OK;

  jc_boot_set_phase(JC_BOOT_PHASE_DISCOVERY);
  err = jc_discovery_init(&g_ctx.anchor, &g_ctx.discovery);
  if (err != JC_E_OK) {
    jc_boot_record_error(JC_BOOT_PHASE_DISCOVERY, err);
    return;
  }
  if (g_ctx.discovery->profile_id != JC_PROFILE_CPU_ONLY &&
      g_ctx.discovery->profile_id != JC_PROFILE_MCU &&
      g_ctx.discovery->profile_id != JC_PROFILE_SOC_RETRO &&
      g_ctx.discovery->profile_id != JC_PROFILE_SOC_WORKSTATION) {
    jc_boot_record_error(JC_BOOT_PHASE_DISCOVERY, JC_E_BOOT_UNSUPPORTED_PROFILE);
    return;
  }

  jc_boot_set_phase(JC_BOOT_PHASE_BDT);
  err = jc_bdt_init(&g_ctx.bdt_index, g_ctx.discovery->bdt_ptr);
  if (err != JC_E_OK) {
    jc_boot_record_error(JC_BOOT_PHASE_BDT, err);
    return;
  }

  jc_boot_set_phase(JC_BOOT_PHASE_TIMER);
  err = jc_timer_init();
  if (err != JC_E_OK) {
    jc_boot_record_error(JC_BOOT_PHASE_TIMER, err);
    return;
  }

  jc_boot_set_phase(JC_BOOT_PHASE_CONSOLE);
  err = jc_console_init();
  if (err != JC_E_OK) {
    jc_boot_record_error(JC_BOOT_PHASE_CONSOLE, err);
    return;
  }

  jc_boot_set_phase(JC_BOOT_PHASE_CAPSET);
  err = jc_capset_init(&g_ctx.capset, g_ctx.discovery, &g_ctx.bdt_index);
  if (err != JC_E_OK) {
    jc_boot_record_error(JC_BOOT_PHASE_CAPSET, err);
    return;
  }
  g_ctx.capset_crc32 =
      jc_crc32((const jc_u8 *)&g_ctx.capset, g_ctx.capset.size_bytes);

  jc_mode_init(JC_TIER_Z80_P0, g_ctx.capset.presented_cpu_tier);

#if !defined(JC_CONFORMANCE_V0_1) && !defined(JC_CONFORMANCE_V0_2) && \
    !defined(JC_CONFORMANCE_V0_3) && !defined(JC_CONFORMANCE_V0_4) && \
    !defined(JC_CONFORMANCE_V0_5) && !defined(JC_CONFORMANCE_V0_6)
  jc_boot_print_header();
#endif

#if defined(JC_CONFORMANCE_V0_1)
  jc_conformance_v0_1();
  for (;;)
    ;
#elif defined(JC_CONFORMANCE_V0_2)
  jc_conformance_v0_2();
  for (;;)
    ;
#elif defined(JC_CONFORMANCE_V0_3)
  jc_conformance_v0_3();
  for (;;)
    ;
#elif defined(JC_CONFORMANCE_V0_4)
  jc_conformance_v0_4();
  for (;;)
    ;
#elif defined(JC_CONFORMANCE_V0_5)
  jc_conformance_v0_5();
  for (;;)
    ;
#elif defined(JC_CONFORMANCE_V0_6)
  jc_conformance_v0_6();
  for (;;)
    ;
#else
  jc_boot_set_phase(JC_BOOT_PHASE_MONITOR);
  jc_monitor_run();
#endif
}
