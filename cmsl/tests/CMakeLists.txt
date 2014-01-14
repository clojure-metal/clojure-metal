cmake_minimum_required(VERSION 2.8)


file(GLOB clojure-metal-tests
   "*.h"
   "*.cpp"
)

SET(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11")

include_directories(../)
include_directories(../../../gtest/fused-src/)
include_directories(../../../mps/code)
link_directories(${CLOJURE_METAL_BINARY_DIR})


add_executable(test ${clojure-metal-tests} ../../../gtest/fused-src/gtest/gtest-all.cc ../../../mps/code/mps.c)

target_link_libraries(test cmsl)
