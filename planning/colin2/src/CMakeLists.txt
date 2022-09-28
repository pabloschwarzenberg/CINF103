cmake_minimum_required(VERSION 2.4)
if(COMMAND cmake_policy)
    cmake_policy(SET CMP0003 NEW)
endif(COMMAND cmake_policy)

project(buildroot)

set(DOXYFILE_IN ${CMAKE_CURRENT_SOURCE_DIR}/Doxyfile.in)

set(CMAKE_CXX_FLAGS_PROFILE "-g3 -pg -O3 -fprofile-arcs")
set(CMAKE_CXX_LINK_FLAGS_PROFILE "-pg")

add_subdirectory(VALfiles)

if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/colin")
	add_subdirectory(colin)
endif(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/colin")


