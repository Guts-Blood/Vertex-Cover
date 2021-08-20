cmake_minimum_required(VERSION 2.8)
project(prjece650)

if (EXISTS "${CMAKE_SOURCE_DIR}/minisat")
  add_subdirectory(minisat)
else()
  message (FATAL_ERROR "MiniSat not found. Use `git clone https://github.com/agurfinkel/minisat` to check it out.")
endif()


## ECE650 Specific configuration start here
## Project specific configurations go here
add_definitions(-D__STDC_FORMAT_MACROS -D__STDC_LIMIT_MACROS)
# enable c++11 support
set (CMAKE_CXX_FLAGS "-std=c++11 -pthread -Wall ${CMAKE_CXX_FLAGS}")
set (CMAKE_C_FLAGS "${CMAKE_CXX_FLAGS} -pthread")

set (CMAKE_EXPORT_COMPILE_COMMANDS ON)

# expose minisat header files
include_directories(${CMAKE_SOURCE_DIR}/minisat)

# create the main executable
## add additional .cpp files if needed
add_executable(prjece650 prjece650.cpp)
add_executable(test test.cpp)
# link MiniSAT libraries
target_link_libraries(prjece650 minisat-lib-static)
target_link_libraries(test minisat-lib-static)