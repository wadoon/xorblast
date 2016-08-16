cmake_minimum_required(VERSION 3.0)

include(ExternalProject)

file(GLOB M4RI_FILES
  m4ri/m4ri/*.c)

#message("-- ${M4RI_FILES}")

ExternalProject_Add(extm4ri
  SOURCE_DIR "${CMAKE_SOURCE_DIR}/m4ri/"
  BUILD_IN_SOURCE 1
  CONFIGURE_COMMAND
    autoreconf --install && ./configure
  INSTALL_COMMAND echo
#  BUILD_COMMAND
#    make -j 2
)

find_package(PNG)

set(CMAKE_CXX_FLAGS "-std=c++11")
set(CMAKE_C_FLAGS "-std=c99")

include_directories("m4ri/")

add_library(m4ri STATIC ${M4RI_FILES})
add_dependencies(m4ri extm4ri)

add_executable(xorblastpp xorblast.cpp)
target_link_libraries(xorblastpp m4ri ${PNG_LIBRARIES})
