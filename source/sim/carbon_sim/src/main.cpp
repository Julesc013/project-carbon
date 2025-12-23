#include <iostream>
#include <limits>
#include <optional>
#include <stdexcept>
#include <string>
#include <string_view>
#include <vector>

#include "carbon_sim/platforms/carbonz.h"
#include "carbon_sim/platforms/cpm22.h"
#include "carbon_sim/platforms/romwbw.h"
#include "carbon_sim/platforms/machine.h"
#include "carbon_sim/rtl/verilator_backend.h"
#include "carbon_sim/sim_config.h"

static void print_usage(std::string_view exe) {
  std::cerr << "Usage: " << exe << " [options]\n\n"
            << "Options:\n"
            << "  --help              Show this help\n"
            << "  --version           Show version\n"
            << "  --platform P        cpm22|romwbw|carbonz80|carbonz90|carbonz380|carbonz480\n"
            << "  --rom PATH          ROM image path\n"
            << "  --disk0 PATH        Disk image path (raw .dsk)\n"
            << "  --disk1 PATH        Optional disk1 path\n"
            << "  --disk2 PATH        Optional disk2 path\n"
            << "  --disk3 PATH        Optional disk3 path\n"
            << "  --trace             Instruction trace\n"
            << "  --max-cycles N      Deterministic cycle limit (0=unlimited)\n"
            << "  --turbo             Faster host execution\n"
            << "  --verilator         Use RTL backend if available\n";
}

static std::string basename(std::string path) {
  const auto slash = path.find_last_of("/\\");
  if (slash == std::string::npos) {
    return path;
  }
  return path.substr(slash + 1);
}

static bool starts_with(std::string_view s, std::string_view prefix) {
  return s.size() >= prefix.size() && s.substr(0, prefix.size()) == prefix;
}

static std::optional<std::string> get_opt_value(std::string_view arg, std::string_view key) {
  if (arg == key) {
    return std::nullopt;
  }
  const std::string k = std::string(key) + "=";
  if (starts_with(arg, k)) {
    return std::string(arg.substr(k.size()));
  }
  return std::nullopt;
}

static std::uint64_t parse_u64(const std::string& s) {
  std::uint64_t v = 0;
  for (char ch : s) {
    if (ch < '0' || ch > '9') {
      throw std::runtime_error("invalid integer: " + s);
    }
    const std::uint64_t digit = static_cast<std::uint64_t>(ch - '0');
    if (v > (std::numeric_limits<std::uint64_t>::max() - digit) / 10) {
      throw std::runtime_error("integer overflow: " + s);
    }
    v = v * 10 + digit;
  }
  return v;
}

static int run_machine(carbon_sim::Machine& machine, const carbon_sim::SimConfig& cfg) {
  machine.bus.reset();
  machine.cpu->reset();

  std::uint64_t cycles = 0;

  auto drain_stdin = [&] {
    if (machine.carbonio == nullptr && machine.uart0 == nullptr && machine.sio0 == nullptr) {
      return;
    }
    while (std::cin.good() && std::cin.rdbuf()->in_avail() > 0) {
      const int ch = std::cin.get();
      if (ch == EOF) {
        break;
      }
      const char c = static_cast<char>(ch);
      if (machine.carbonio != nullptr) {
        machine.carbonio->feed_input(std::string_view(&c, 1));
      } else if (machine.uart0 != nullptr) {
        machine.uart0->feed_input(std::string_view(&c, 1));
      } else if (machine.sio0 != nullptr) {
        machine.sio0->feed_input(std::string_view(&c, 1));
      }
    }
  };

  const int batch_instr = cfg.turbo ? 512 : 1;
  while (!machine.cpu->trapped()) {
    if (cfg.max_cycles != 0 && cycles >= cfg.max_cycles) {
      break;
    }

    drain_stdin();

    std::uint64_t batch_cycles = 0;
    for (int i = 0; i < batch_instr && !machine.cpu->trapped(); ++i) {
      if (cfg.max_cycles != 0 && cycles + batch_cycles >= cfg.max_cycles) {
        break;
      }
      const auto step = machine.cpu->step();
      if (step == 0) {
        break;
      }
      batch_cycles += step;
      if (machine.cpu->halted()) {
        break;
      }
    }

    if (batch_cycles != 0) {
      machine.bus.tick(batch_cycles);
      cycles += batch_cycles;
    }

    if (machine.cpu->halted()) {
      break;
    }
  }

  if (machine.cpu->trapped()) {
    std::cerr << "TRAP: " << machine.cpu->trap_reason() << " (PC=" << std::hex << std::uppercase
              << machine.cpu->pc() << ")\n";
    return 1;
  }
  return 0;
}

int main(int argc, char** argv) {
  const std::string exe = argc > 0 ? basename(argv[0]) : "carbon-sim";
  const std::vector<std::string> args(argv + 1, argv + argc);

  carbon_sim::SimConfig cfg;

  for (const auto& arg : args) {
    if (arg == "--help" || arg == "-h") {
      print_usage(exe);
      return 0;
    }
    if (arg == "--version") {
      std::cout << "carbon-sim (project-carbon)\n";
      return 0;
    }
  }

  try {
    for (std::size_t i = 0; i < args.size(); ++i) {
      const auto& arg = args[i];

      if (arg == "--trace") {
        cfg.trace = true;
        continue;
      }
      if (arg == "--turbo") {
        cfg.turbo = true;
        continue;
      }
      if (arg == "--verilator") {
        cfg.verilator = true;
        continue;
      }

      if (auto v = get_opt_value(arg, "--platform"); v.has_value()) {
        cfg.platform = *v;
        continue;
      }
      if (arg == "--platform") {
        if (i + 1 >= args.size()) {
          throw std::runtime_error("--platform requires a value");
        }
        cfg.platform = args[++i];
        continue;
      }

      if (auto v = get_opt_value(arg, "--rom"); v.has_value()) {
        cfg.rom_path = *v;
        continue;
      }
      if (arg == "--rom") {
        if (i + 1 >= args.size()) {
          throw std::runtime_error("--rom requires a value");
        }
        cfg.rom_path = args[++i];
        continue;
      }

      for (int d = 0; d < 4; ++d) {
        const std::string key = "--disk" + std::to_string(d);
        if (auto v = get_opt_value(arg, key); v.has_value()) {
          cfg.disk_paths[static_cast<std::size_t>(d)] = *v;
          goto parsed;
        }
        if (arg == key) {
          if (i + 1 >= args.size()) {
            throw std::runtime_error(key + " requires a value");
          }
          cfg.disk_paths[static_cast<std::size_t>(d)] = args[++i];
          goto parsed;
        }
      }

      if (auto v = get_opt_value(arg, "--max-cycles"); v.has_value()) {
        cfg.max_cycles = parse_u64(*v);
        continue;
      }
      if (arg == "--max-cycles") {
        if (i + 1 >= args.size()) {
          throw std::runtime_error("--max-cycles requires a value");
        }
        cfg.max_cycles = parse_u64(args[++i]);
        continue;
      }

      if (!arg.empty() && arg[0] == '-') {
        throw std::runtime_error("unknown option: " + arg);
      }

    parsed:
      continue;
    }

    if (cfg.platform.empty()) {
      throw std::runtime_error("--platform is required");
    }

    if (cfg.verilator) {
      if (!carbon_sim::VerilatorBackend::built()) {
        throw std::runtime_error("built without Verilator backend support; configure with -DCARBON_SIM_ENABLE_VERILATOR=ON");
      }
      return carbon_sim::VerilatorBackend::run(cfg);
    }

    std::unique_ptr<carbon_sim::Machine> machine;
    if (cfg.platform == "cpm22") {
      machine = carbon_sim::create_platform_cpm22(cfg, std::cout);
    } else if (cfg.platform == "romwbw") {
      machine = carbon_sim::create_platform_romwbw(cfg, std::cout);
    } else if (cfg.platform == "carbonz80") {
      machine = carbon_sim::create_platform_carbonz80(cfg, std::cout);
    } else if (cfg.platform == "carbonz90") {
      machine = carbon_sim::create_platform_carbonz90(cfg, std::cout);
    } else if (cfg.platform == "carbonz380") {
      machine = carbon_sim::create_platform_carbonz380(cfg, std::cout);
    } else if (cfg.platform == "carbonz480") {
      machine = carbon_sim::create_platform_carbonz480(cfg, std::cout);
    } else {
      throw std::runtime_error("unknown platform: " + cfg.platform);
    }

    return run_machine(*machine, cfg);
  } catch (const std::exception& e) {
    std::cerr << "error: " << e.what() << "\n\n";
    print_usage(exe);
    return 2;
  }
}
