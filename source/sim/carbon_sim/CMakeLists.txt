cmake_minimum_required(VERSION 3.20)

project(carbon_sim LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

add_executable(carbon-sim
  src/main.cpp
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
