cmake_minimum_required(VERSION 3.20)

project(carbon_sim LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

add_library(carbon_sim_core
  src/block_disk.cpp
  src/boot_rom.cpp
  src/cpm_disk.cpp
  src/ide_disk.cpp
  src/interrupt_controller.cpp
  src/platform_cpm22.cpp
  src/platform_romwbw.cpp
  src/timer_tick.cpp
  src/uart_console.cpp
  src/zilog_sio.cpp
  src/z80.cpp
)

target_include_directories(carbon_sim_core PUBLIC
  ${CMAKE_CURRENT_SOURCE_DIR}/include
)

if(MSVC)
  target_compile_options(carbon_sim_core PUBLIC /W4 /permissive-)
else()
  target_compile_options(carbon_sim_core PUBLIC -Wall -Wextra -Wpedantic)
endif()

add_executable(carbon-sim
  src/main.cpp
)
target_link_libraries(carbon-sim PRIVATE carbon_sim_core)

enable_testing()

add_executable(carbon-sim-smoke
  tests/smoke.cpp
)
target_link_libraries(carbon-sim-smoke PRIVATE carbon_sim_core)
add_test(NAME carbon-sim-smoke COMMAND carbon-sim-smoke)
