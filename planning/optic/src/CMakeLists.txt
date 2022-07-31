cmake_minimum_required(VERSION 2.4)
if(COMMAND cmake_policy)
    cmake_policy(SET CMP0003 NEW)
endif(COMMAND cmake_policy)

project(buildroot)

set(DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/Doxyfile.in)

set(CMAKE_CXX_FLAGS_PROFILE "-g3 -pg -O -fprofile-arcs")
set(CMAKE_CXX_LINK_FLAGS_PROFILE "-pg")

add_subdirectory(VALfiles)


if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/optic")
	add_subdirectory(optic)
endif(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/optic")


