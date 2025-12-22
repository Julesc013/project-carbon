#pragma once

#include <cstdint>

namespace carbon_sim {

constexpr std::uint32_t kBdtSignature = 0x54444243u; // "CBDT" little-endian
constexpr std::uint16_t kBdtHeaderVersion = 1;
constexpr std::uint16_t kBdtHeaderSizeBytes = 16;
constexpr std::uint16_t kBdtEntrySizeBytes = 64;

constexpr std::uint16_t kDevClassCpu = 0x0001;
constexpr std::uint16_t kDevClassFpu = 0x0002;
constexpr std::uint16_t kDevClassUart = 0x0010;
constexpr std::uint16_t kDevClassSio = 0x0011;
constexpr std::uint16_t kDevClassPio = 0x0012;
constexpr std::uint16_t kDevClassTimer = 0x0013;
constexpr std::uint16_t kDevClassIrqCtrl = 0x0014;
constexpr std::uint16_t kDevClassDma = 0x0020;
constexpr std::uint16_t kDevClassBlockStorage = 0x0030;
constexpr std::uint16_t kDevClassCharStorage = 0x0031;

constexpr std::uint32_t kCompatPolling = (1u << 0);
constexpr std::uint32_t kCompatIrq = (1u << 1);
constexpr std::uint32_t kCompatPortIo = (1u << 2);
constexpr std::uint32_t kCompatMmio = (1u << 3);
constexpr std::uint32_t kCompatWait = (1u << 4);

constexpr std::uint32_t kTurboQueue = (1u << 0);
constexpr std::uint32_t kTurboDma = (1u << 1);
constexpr std::uint32_t kTurboTimestamps = (1u << 2);
constexpr std::uint32_t kTurboPerf = (1u << 3);
constexpr std::uint32_t kTurboWatermarkIrq = (1u << 4);

constexpr std::uint32_t kFeatCapsMask = (1u << 5);
constexpr std::uint32_t kFeatDeviceModelMask = (1u << 8);
constexpr std::uint32_t kFeatBdtMask = (1u << 9);
constexpr std::uint32_t kFeatPollingCompleteMask = (1u << 11);

constexpr unsigned kFeatWord0RxFifoLsb = 0;
constexpr unsigned kFeatWord0TxFifoLsb = 8;
constexpr unsigned kFeatWord0DmaChannelsLsb = 16;
constexpr unsigned kFeatWord0TimerCountLsb = 24;

constexpr unsigned kFeatWord1TimestampBitsLsb = 0;
constexpr unsigned kFeatWord1QueueCountLsb = 8;
constexpr unsigned kFeatWord1QueueDepthLsb = 16;

} // namespace carbon_sim
