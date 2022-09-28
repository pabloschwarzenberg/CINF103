#!/bin/bash
apt-get update
apt-get -y install gcc g++ doxygen bison flex
apt-get -y install cmake
apt-get -y install zlib1g-dev
apt-get -y install libgsl-dev
apt-get -y install coinor-libcbc-dev coinor-libclp-dev coinor-libcoinutils-dev coinor-libosi-dev coinor-libcgl-dev
./run-cmake-release
./build-release
