cmake_minimum_required(VERSION 3.20)

project(carbon_sim LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

add_library(carbon_sim_core
  src/bsp_loader.cpp
  src/bdt_builder.cpp
  src/block_disk.cpp
  src/boot_rom.cpp
  src/carbon_mmio.cpp
  src/caps.cpp
  src/carbondma.cpp
  src/carbonio.cpp
  src/cpm_disk.cpp
  src/ide_disk.cpp
  src/interrupt_controller.cpp
  src/platform_carbonz.cpp
  src/platform_cpm22.cpp
  src/platform_romwbw.cpp
  src/tier_host_stub.cpp
  src/timer_tick.cpp
  src/uart_console.cpp
  src/verilator_backend.cpp
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

option(CARBON_SIM_ENABLE_VERILATOR "Enable Verilator RTL backend (preview scaffolding)" OFF)
if(CARBON_SIM_ENABLE_VERILATOR)
  find_program(VERILATOR_BIN verilator)
  if(NOT VERILATOR_BIN)
    message(FATAL_ERROR "CARBON_SIM_ENABLE_VERILATOR=ON but 'verilator' was not found in PATH")
  endif()

  if(NOT DEFINED ENV{VERILATOR_ROOT})
    message(FATAL_ERROR "CARBON_SIM_ENABLE_VERILATOR=ON but VERILATOR_ROOT is not set")
  endif()
  set(VERILATOR_ROOT $ENV{VERILATOR_ROOT})

  target_include_directories(carbon_sim_core PUBLIC ${VERILATOR_ROOT}/include)
  target_compile_definitions(carbon_sim_core PUBLIC CARBON_SIM_ENABLE_VERILATOR=1)
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
