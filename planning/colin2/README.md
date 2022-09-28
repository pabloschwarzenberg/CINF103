# colin2
The COLIN2 planner from the Planning group at King's College London

- cmake
- perl, bison and flex (used to build the parser)

cmake, perl, and bison can be retrieved through package manager. Flex is more difficult. The current version of flex
(2.6.2 on github.com/westes/flex) does not work with COLIN. For now, we just use a working older version of flex
(2.5.39 at https://sourceforge.net/projects/flex/files/). Download and compile flex. Either ensure that `flex` actually
calls the correct version (`flex --version`) or update src/VALfiles/parsing/CMakeLists with the correct flex executable. 

Other packages are also required:
sudo apt-get install coinor-libcbc-dev coinor-libclp-dev coinor-libcoinutils-dev libbz2-dev

To build:
```
./run-cmake-release
./build-release
```

If you have multiple cores available, then updating build-release to reflect the number of build processes will speed up
compilation.
