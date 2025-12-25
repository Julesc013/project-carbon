#include "jc_block.h"

#include "jc_bdt.h"
#include "jc_bios.h"
#include "jc_contracts_autogen.h"
#include "jc_timer.h"
#include "jc_util.h"

typedef struct {
  jc_u32 io_base;
  jc_u16 io_size;
  jc_u16 sector_size;
  jc_u32 timeout_ticks;
  jc_u32 total_sectors;
  int open;
} jc_idepio_alt1_dev;

static jc_idepio_alt1_dev g_dev;

static jc_u8 jc_io_read8(jc_u32 base, jc_u8 reg) {
  volatile jc_u8 *ptr = (volatile jc_u8 *)(unsigned long)(base + reg);
  return *ptr;
}

static void jc_io_write8(jc_u32 base, jc_u8 reg, jc_u8 value) {
  volatile jc_u8 *ptr = (volatile jc_u8 *)(unsigned long)(base + reg);
  *ptr = value;
}

static jc_u8 jc_idepio_status(jc_idepio_alt1_dev *dev) {
  return jc_io_read8(dev->io_base, JC_IDEPIO_REG_STATUS);
}

static jc_error_t jc_idepio_wait_ready(jc_idepio_alt1_dev *dev,
                                       jc_u64 deadline) {
  while (!jc_timer_expired(deadline)) {
    jc_u8 status = jc_idepio_status(dev);
    if (status & JC_IDEPIO_STATUS_ERR_MASK) {
      return JC_E_DEV_IO_ERROR;
    }
    if ((status & JC_IDEPIO_STATUS_BSY_MASK) == 0 &&
        (status & JC_IDEPIO_STATUS_DRDY_MASK) != 0) {
      return JC_E_OK;
    }
  }
  return JC_E_DEV_IO_TIMEOUT;
}

static jc_error_t jc_idepio_wait_drq(jc_idepio_alt1_dev *dev,
                                     jc_u64 deadline) {
  while (!jc_timer_expired(deadline)) {
    jc_u8 status = jc_idepio_status(dev);
    if (status & JC_IDEPIO_STATUS_ERR_MASK) {
      return JC_E_DEV_IO_ERROR;
    }
    if ((status & JC_IDEPIO_STATUS_BSY_MASK) == 0 &&
        (status & JC_IDEPIO_STATUS_DRQ_MASK) != 0) {
      return JC_E_OK;
    }
  }
  return JC_E_DEV_IO_TIMEOUT;
}

static void jc_idepio_select_lba(jc_idepio_alt1_dev *dev, jc_u32 lba) {
  jc_u8 drive_head = (jc_u8)(0xE0u | ((lba >> 24) & 0x0Fu));
  jc_io_write8(dev->io_base, JC_IDEPIO_REG_DRIVE_HEAD, drive_head);
}

static jc_error_t jc_idepio_identify(jc_idepio_alt1_dev *dev) {
  jc_u8 data[512];
  jc_u32 i;
  jc_error_t err;

  jc_idepio_select_lba(dev, 0);
  err = jc_idepio_wait_ready(dev,
                              jc_timer_deadline_from_now(dev->timeout_ticks));
  if (err != JC_E_OK) {
    return err;
  }

  jc_io_write8(dev->io_base, JC_IDEPIO_REG_COMMAND,
               (jc_u8)JC_IDEPIO_CMD_IDENTIFY);
  err = jc_idepio_wait_drq(dev,
                            jc_timer_deadline_from_now(dev->timeout_ticks));
  if (err != JC_E_OK) {
    return err;
  }

  for (i = 0; i < sizeof(data); ++i) {
    data[i] = jc_io_read8(dev->io_base, JC_IDEPIO_REG_DATA);
  }

  dev->total_sectors =
      (jc_u32)data[120] | ((jc_u32)data[121] << 8) |
      ((jc_u32)data[122] << 16) | ((jc_u32)data[123] << 24);

  return JC_E_OK;
}

jc_error_t jc_storage_validate_entry(const jc_bdt_entry_v1 *entry) {
  if (!entry) {
    return JC_E_INTERNAL_ASSERT;
  }
  if (entry->class_id != JC_DEVCLASS_STORAGE) {
    return JC_E_DEV_UNSUPPORTED;
  }
  if ((entry->caps0 & JC_DEV_COMPAT_PORT_IO_MASK) == 0u) {
    return JC_E_DEV_UNSUPPORTED;
  }
  if (entry->io_port_base == 0u || entry->io_port_size < 8u) {
    return JC_E_DEV_UNSUPPORTED;
  }
  if (entry->block_sector_size != 512u) {
    return JC_E_DEV_UNSUPPORTED;
  }
  if (entry->caps1 == 0u) {
    return JC_E_DEV_UNSUPPORTED;
  }
  return JC_E_OK;
}

jc_error_t jc_blk_open(jc_u16 instance) {
  const jc_bdt_index *bdt = 0;
  const jc_bdt_entry_v1 *entry = 0;
  jc_error_t err;

  if (g_dev.open) {
    return JC_E_OK;
  }
  bdt = jc_boot_bdt_index();
  if (!bdt) {
    return JC_E_BDT_BAD_SIZE;
  }
  entry = jc_bdt_find(bdt, JC_DEVCLASS_STORAGE, instance);
  if (!entry) {
    return JC_E_DEV_NOT_FOUND;
  }

  err = jc_storage_validate_entry(entry);
  if (err != JC_E_OK) {
    return err;
  }

  g_dev.io_base = entry->io_port_base;
  g_dev.io_size = entry->io_port_size;
  g_dev.sector_size = entry->block_sector_size;
  g_dev.timeout_ticks = entry->caps1;
  g_dev.total_sectors = 0;
  g_dev.open = 1;

  err = jc_idepio_identify(&g_dev);
  if (err != JC_E_OK) {
    g_dev.open = 0;
  }
  return err;
}

static jc_error_t jc_idepio_pio_read(jc_idepio_alt1_dev *dev,
                                     jc_u32 lba,
                                     jc_u8 *buf,
                                     jc_u16 count) {
  jc_u16 sector;
  jc_error_t err;

  jc_idepio_select_lba(dev, lba);
  err = jc_idepio_wait_ready(dev,
                              jc_timer_deadline_from_now(dev->timeout_ticks));
  if (err != JC_E_OK) {
    return err;
  }

  jc_io_write8(dev->io_base, JC_IDEPIO_REG_SECTOR_COUNT, (jc_u8)count);
  jc_io_write8(dev->io_base, JC_IDEPIO_REG_SECTOR_NUMBER, (jc_u8)(lba & 0xFFu));
  jc_io_write8(dev->io_base, JC_IDEPIO_REG_CYLINDER_LOW,
               (jc_u8)((lba >> 8) & 0xFFu));
  jc_io_write8(dev->io_base, JC_IDEPIO_REG_CYLINDER_HIGH,
               (jc_u8)((lba >> 16) & 0xFFu));
  jc_idepio_select_lba(dev, lba);
  jc_io_write8(dev->io_base, JC_IDEPIO_REG_COMMAND,
               (jc_u8)JC_IDEPIO_CMD_READ_SECTORS);

  for (sector = 0; sector < count; ++sector) {
    jc_u32 i;
    err = jc_idepio_wait_drq(
        dev, jc_timer_deadline_from_now(dev->timeout_ticks));
    if (err != JC_E_OK) {
      return err;
    }
    for (i = 0; i < 512u; ++i) {
      buf[sector * 512u + i] =
          jc_io_read8(dev->io_base, JC_IDEPIO_REG_DATA);
    }
  }
  return JC_E_OK;
}

static jc_error_t jc_idepio_pio_write(jc_idepio_alt1_dev *dev,
                                      jc_u32 lba,
                                      const jc_u8 *buf,
                                      jc_u16 count) {
  jc_u16 sector;
  jc_error_t err;

  jc_idepio_select_lba(dev, lba);
  err = jc_idepio_wait_ready(dev,
                              jc_timer_deadline_from_now(dev->timeout_ticks));
  if (err != JC_E_OK) {
    return err;
  }

  jc_io_write8(dev->io_base, JC_IDEPIO_REG_SECTOR_COUNT, (jc_u8)count);
  jc_io_write8(dev->io_base, JC_IDEPIO_REG_SECTOR_NUMBER, (jc_u8)(lba & 0xFFu));
  jc_io_write8(dev->io_base, JC_IDEPIO_REG_CYLINDER_LOW,
               (jc_u8)((lba >> 8) & 0xFFu));
  jc_io_write8(dev->io_base, JC_IDEPIO_REG_CYLINDER_HIGH,
               (jc_u8)((lba >> 16) & 0xFFu));
  jc_idepio_select_lba(dev, lba);
  jc_io_write8(dev->io_base, JC_IDEPIO_REG_COMMAND,
               (jc_u8)JC_IDEPIO_CMD_WRITE_SECTORS);

  for (sector = 0; sector < count; ++sector) {
    jc_u32 i;
    err = jc_idepio_wait_drq(
        dev, jc_timer_deadline_from_now(dev->timeout_ticks));
    if (err != JC_E_OK) {
      return err;
    }
    for (i = 0; i < 512u; ++i) {
      jc_io_write8(dev->io_base, JC_IDEPIO_REG_DATA,
                   buf[sector * 512u + i]);
    }
  }
  return JC_E_OK;
}

jc_error_t jc_blk_read(jc_u32 lba, jc_u8 *buf, jc_u16 count512) {
  jc_u16 remaining = count512;
  jc_u32 current_lba = lba;
  jc_u8 *dst = buf;

  if (!buf || count512 == 0) {
    return JC_E_INTERNAL_ASSERT;
  }
  if (!g_dev.open) {
    return JC_E_DEV_NOT_FOUND;
  }
  while (remaining > 0) {
    jc_u16 chunk = remaining > 255u ? 255u : remaining;
    jc_error_t err = jc_idepio_pio_read(&g_dev, current_lba, dst, chunk);
    if (err != JC_E_OK) {
      return err;
    }
    remaining = (jc_u16)(remaining - chunk);
    current_lba += chunk;
    dst += (jc_u32)chunk * 512u;
  }
  return JC_E_OK;
}

jc_error_t jc_blk_write(jc_u32 lba, const jc_u8 *buf, jc_u16 count512) {
  jc_u16 remaining = count512;
  jc_u32 current_lba = lba;
  const jc_u8 *src = buf;

  if (!buf || count512 == 0) {
    return JC_E_INTERNAL_ASSERT;
  }
  if (!g_dev.open) {
    return JC_E_DEV_NOT_FOUND;
  }
  while (remaining > 0) {
    jc_u16 chunk = remaining > 255u ? 255u : remaining;
    jc_error_t err = jc_idepio_pio_write(&g_dev, current_lba, src, chunk);
    if (err != JC_E_OK) {
      return err;
    }
    remaining = (jc_u16)(remaining - chunk);
    current_lba += chunk;
    src += (jc_u32)chunk * 512u;
  }
  return JC_E_OK;
}

jc_error_t jc_blk_get_params(jc_block_params *out_params) {
  if (!out_params) {
    return JC_E_INTERNAL_ASSERT;
  }
  if (!g_dev.open) {
    return JC_E_DEV_NOT_FOUND;
  }
  out_params->block_size_bytes = 512u;
  out_params->max_sectors_per_op = 255u;
  out_params->total_sectors = g_dev.total_sectors;
  out_params->timeout_ticks = g_dev.timeout_ticks;
  return JC_E_OK;
}

jc_error_t jc_blk_self_test(void) {
  jc_u8 buf[512];
  jc_error_t err = jc_blk_open(0);
  if (err != JC_E_OK) {
    return err;
  }
  return jc_blk_read(0, buf, 1);
}

jc_error_t jc_blk_test_timeout(jc_u32 timeout_ticks) {
  jc_u64 deadline = jc_timer_deadline_from_now(timeout_ticks);
  while (!jc_timer_expired(deadline)) {
  }
  return JC_E_DEV_IO_TIMEOUT;
}
