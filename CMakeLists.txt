cmake_minimum_required(VERSION 3.24)
project(c__23)

set(CMAKE_CXX_STANDARD 23)

set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -Wl,--stack,1073741824")

add_executable(c__23 main.cpp)

target_compile_definitions(c__23 PRIVATE LOCAL_TEST)
