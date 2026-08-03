cmake_minimum_required(VERSION 4.3.2 FATAL_ERROR)

foreach(required SOURCE_ROOT SCAN_ROOT EXPECTED_TEXT)
  if(NOT DEFINED ${required})
    message(FATAL_ERROR "ExpectAuditFailure requires ${required}")
  endif()
endforeach()

execute_process(
  COMMAND
    "${CMAKE_COMMAND}"
    -DSOURCE_ROOT=${SOURCE_ROOT}
    -DSCAN_ROOT=${SCAN_ROOT}
    -P "${SOURCE_ROOT}/cmake/HolonicAudit.cmake"
  RESULT_VARIABLE result
  OUTPUT_VARIABLE output
  ERROR_VARIABLE error)
if(result EQUAL 0)
  message(FATAL_ERROR "forbidden audit fixture unexpectedly passed: ${SCAN_ROOT}")
endif()
set(diagnostic "${output}\n${error}")
if(NOT diagnostic MATCHES "${EXPECTED_TEXT}")
  message(FATAL_ERROR "forbidden audit fixture failed unexpectedly: ${diagnostic}")
endif()
message(STATUS "forbidden audit fixture failed as required: ${SCAN_ROOT}")
