cmake_minimum_required(VERSION 2.8.6)

set(CMAKE_MODULE_PATH "${CMAKE_SOURCE_DIR}/cmake")

find_package(M4RI)
find_package(PNG)

set(CMAKE_CXX_FLAGS "-std=c++11")
set(CMAKE_C_FLAGS "-std=c99")

add_executable(xorblastpp xorblast.cpp)
target_link_libraries(xorblastpp m4ri ${PNG_LIBRARIES})
