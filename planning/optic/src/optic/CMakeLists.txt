PROJECT(optic)

set( CMAKE_MODULE_PATH    ${CMAKE_MODULE_PATH}
                          ${CMAKE_CURRENT_SOURCE_DIR}
                          ${CMAKE_CURRENT_SOURCE_DIR}/cmake/modules
                          ${CMAKE_CURRENT_SOURCE_DIR}/../cmake/modules)


set(DOXYFILE_TARGET_SUFFIX optic)
include(UseDoxygen OPTIONAL)


find_package(Clp)
find_package(CoinUtils)
find_package(Cbc)
find_package(Cgl)
find_package(OSI)
find_package(GSL)


set(CMAKE_CXX_FLAGS "-Wall ${CMAKE_CXX_FLAGS}")

if(STATIC_OPTIC)
set(CMAKE_CXX_LINK_FLAGS "-static ${CMAKE_CXX_LINK_FLAGS}")
endif(STATIC_OPTIC)

include_directories(${val_SOURCE_DIR} ${val_SOURCE_DIR}/parsing ${val_BINARY_DIR} ${CLP_INCLUDES}/coin ${CBC_INCLUDES}/coin ${CPLEX_INCLUDES} ${CONCERT_INCLUDES}  ${GSL_INCLUDES})

set(optic_build_srcs
    compressionsafescheduler.cpp
    totalordertransformer.cpp
    partialordertransformer.cpp
    FFSolver.cpp
    FFEvent.cpp
    globals.cpp
    lpscheduler.cpp
    RPGBuilder.cpp
    RPGBuilderAnalysis.cpp
    RPGBuilderEvaluation.cpp
    RPGBuilderNumerics.cpp
    temporalanalysis.cpp
    minimalstate.cpp
    temporalconstraints.cpp
    numericanalysis.cpp
    solver.cpp
    NNF.cpp
    PreferenceHandler.cpp
    choosepreconditions.cpp)

add_library(OpticCommon STATIC ${optic_build_srcs})
target_link_libraries(OpticCommon ParsePDDL Inst)
SET_TARGET_PROPERTIES(OpticCommon PROPERTIES COMPILE_FLAGS "-DPOPF3ANALYSIS")

if (CLP_INCLUDES AND CBC_INCLUDES)

    ADD_EXECUTABLE(optic-clp opticMain.cpp solver-clp.cpp)
    
    target_link_libraries(optic-clp
        OpticCommon
        ${CBC_SOLVER_LIBRARY} ${CBC_LIBRARY} ${CGL_LIBRARIES} ${OSICLP_LIBRARIES} ${OSI_LIBRARIES} ${CLP_LIBRARIES}  ${COINUTILS_LIBRARIES} -lz -lbz2
    )
    SET_TARGET_PROPERTIES(optic-clp PROPERTIES COMPILE_FLAGS "-DPOPF3ANALYSIS")

endif(CLP_INCLUDES AND CBC_INCLUDES)

if(CPLEX AND ILOCPLEX AND CONCERT AND CPLEX_INCLUDES AND CONCERT_INCLUDES)

    ADD_EXECUTABLE(optic-cplex opticMain.cpp solver-cpx.cpp)
    
    target_link_libraries(optic-cplex    
            OpticCommon
            ${ILOCPLEX} ${CPLEX} ${CONCERT} pthread
    )
    SET_TARGET_PROPERTIES(optic-cplex PROPERTIES COMPILE_FLAGS "-DPOPF3ANALYSIS")
    
endif(CPLEX AND ILOCPLEX AND CONCERT AND CPLEX_INCLUDES AND CONCERT_INCLUDES)

