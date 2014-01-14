cmake_minimum_required(VERSION 2.8)

file(GLOB clojure-metal
    "*.h"
    "*.c"
    "*.cpp"
)

SET(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11")

include_directories(../../../mps/code)
include_directories(../)
add_library(cmsl ${clojure-metal})
