# include(FindLibraryWithDebug)

if (GSL_INCLUDES AND GSL_LIBRARIES)
  set(GSL_FIND_QUIETLY TRUE)
endif (GSL_INCLUDES AND GSL_LIBRARIES)

find_path(GSL_INCLUDES
  NAMES
  gsl/gsl_cdf.h
  PATHS
  $ENV{GSLDIR}/include
  ${INCLUDE_INSTALL_DIR}
)

find_library(GSL_LIBRARIES
  gsl
  PATHS
  $ENV{GSLDIR}/lib
  ${LIB_INSTALL_DIR}
)

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(GSL DEFAULT_MSG
                                  GSL_INCLUDES GSL_LIBRARIES)

mark_as_advanced(GSL_INCLUDES GSL_LIBRARIES)

