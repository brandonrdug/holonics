cmake_minimum_required(VERSION 4.3.2 FATAL_ERROR)

foreach(required COMPILER SOURCE INCLUDE_DIRECTORY EXPECTED_TEXT)
  if(NOT DEFINED ${required})
    message(FATAL_ERROR "ExpectCompileFailure requires ${required}")
  endif()
endforeach()

execute_process(
  COMMAND
    "${COMPILER}" -std=c++23 -fsyntax-only -I "${INCLUDE_DIRECTORY}" "${SOURCE}"
  RESULT_VARIABLE result
  OUTPUT_VARIABLE output
  ERROR_VARIABLE error)
if(result EQUAL 0)
  message(FATAL_ERROR "forbidden compile fixture unexpectedly compiled: ${SOURCE}")
endif()
set(diagnostic "${output}\n${error}")
if(NOT diagnostic MATCHES "${EXPECTED_TEXT}")
  message(FATAL_ERROR
    "forbidden compile fixture failed for an unexpected reason: ${diagnostic}")
endif()
message(STATUS "forbidden compile fixture failed as required: ${SOURCE}")
