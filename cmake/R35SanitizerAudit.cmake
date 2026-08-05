cmake_minimum_required(VERSION 4.3.2 FATAL_ERROR)
foreach(required IN ITEMS DISCOVERY_MEMCHECK DISCOVERY_INITCHECK APPLICATION_MEMCHECK
    APPLICATION_INITCHECK DISCOVERY_MEMCHECK_DEED DISCOVERY_INITCHECK_DEED
    APPLICATION_MEMCHECK_DEED APPLICATION_INITCHECK_DEED OUTPUT)
  if(NOT DEFINED ${required})
    message(FATAL_ERROR "R35 sanitizer audit requires ${required}")
  endif()
endforeach()
foreach(required IN ITEMS DISCOVERY_MEMCHECK DISCOVERY_INITCHECK APPLICATION_MEMCHECK
    APPLICATION_INITCHECK)
  file(READ "${${required}}" report)
  string(FIND "${report}" "ERROR SUMMARY: 0 errors" zero_position)
  if(zero_position EQUAL -1)
    message(FATAL_ERROR "R35 sanitizer report ${required} did not return zero errors")
  endif()
endforeach()
foreach(required IN ITEMS DISCOVERY_MEMCHECK_DEED DISCOVERY_INITCHECK_DEED
    APPLICATION_MEMCHECK_DEED APPLICATION_INITCHECK_DEED)
  file(READ "${${required}}" deed)
  foreach(needle IN ITEMS "verification_failures=0" "checker_exit=0")
    string(FIND "${deed}" "${needle}" deed_position)
    if(deed_position EQUAL -1)
      message(FATAL_ERROR "R35 sanitized deed ${required} omits ${needle}")
    endif()
  endforeach()
endforeach()
file(WRITE "${OUTPUT}" "truth_status=established-bounded\n"
  "evidence=implemented-exact,computational-witness\n"
  "discovery_memcheck_errors=0\ndiscovery_initcheck_errors=0\n"
  "application_memcheck_errors=0\napplication_initcheck_errors=0\n"
  "sanitized_deed_verification_failures=0\nsanitized_checker_failures=0\n"
  "tool=compute-sanitizer\ndevice=sm_89\n"
  "physical_telemetry=engine_time:unknown,temperature:unknown,power:unknown,energy:unknown\n")
