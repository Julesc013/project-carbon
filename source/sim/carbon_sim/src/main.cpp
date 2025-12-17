#include <cstdint>
#include <iostream>
#include <string>
#include <string_view>
#include <vector>

static void print_usage(std::string_view exe) {
  std::cerr << "Usage: " << exe << " [options]\n\n"
            << "Options:\n"
            << "  --help              Show this help\n"
            << "  --version           Show version\n";
}

static std::string basename(std::string path) {
  const auto slash = path.find_last_of("/\\");
  if (slash == std::string::npos) {
    return path;
  }
  return path.substr(slash + 1);
}

int main(int argc, char** argv) {
  const std::string exe = argc > 0 ? basename(argv[0]) : "carbon-sim";
  const std::vector<std::string> args(argv + 1, argv + argc);

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

  print_usage(exe);
  return 2;
}

