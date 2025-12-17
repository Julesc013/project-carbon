cmake_minimum_required(VERSION 3.20)

project(carbon_sim LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

add_executable(carbon-sim
  src/block_disk.cpp
  src/boot_rom.cpp
  src/cpm_disk.cpp
  src/ide_disk.cpp
  src/interrupt_controller.cpp
  src/main.cpp
  src/platform_cpm22.cpp
  src/platform_romwbw.cpp
  src/timer_tick.cpp
  src/uart_console.cpp
  src/zilog_sio.cpp
  src/z80.cpp
)

target_include_directories(carbon-sim PRIVATE
  ${CMAKE_CURRENT_SOURCE_DIR}/include
)

if(MSVC)
  target_compile_options(carbon-sim PRIVATE /W4 /permissive-)
else()
  target_compile_options(carbon-sim PRIVATE -Wall -Wextra -Wpedantic)
endif()
