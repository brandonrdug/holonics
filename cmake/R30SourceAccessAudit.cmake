cmake_minimum_required(VERSION 4.3.2 FATAL_ERROR)
foreach(required IN ITEMS EXECUTABLE PROBE LOG OUTPUT SOURCE_ROOT DEED PREDECESSOR HANDOFF
    MATCHING LATTICE COVER SOURCE OLEAN STDOUT STDERR FOIL_SOURCE FOIL_OLEAN FOIL_STDOUT
    FOIL_STDERR FORMAL_ROOT TOOLCHAIN MANIFEST ARTIFACT_ROOT ATLAS DOSSIER)
  if(NOT DEFINED ${required})
    message(FATAL_ERROR "R30 source-access audit requires ${required}")
  endif()
endforeach()
file(REMOVE "${LOG}")
execute_process(COMMAND "${CMAKE_COMMAND}" -E env
  "LD_PRELOAD=${PROBE}" "HOLONICS_R30_OPEN_LOG=${LOG}"
  "${EXECUTABLE}" "${DEED}" "${PREDECESSOR}" "${HANDOFF}"
  "${MATCHING}" "${LATTICE}" "${COVER}"
  "${SOURCE}" "${OLEAN}" "${STDOUT}" "${STDERR}"
  "${FOIL_SOURCE}" "${FOIL_OLEAN}" "${FOIL_STDOUT}" "${FOIL_STDERR}"
  "${FORMAL_ROOT}" "${TOOLCHAIN}" "${MANIFEST}" "${ARTIFACT_ROOT}"
  "${ATLAS}" "${DOSSIER}"
  RESULT_VARIABLE deed_result)
if(NOT deed_result EQUAL 0 OR NOT EXISTS "${LOG}")
  message(FATAL_ERROR "R30 source-access instrumented deed failed")
endif()
file(READ "${LOG}" opened)
foreach(required_open IN ITEMS
    "R29_ARITHMETIC_SPECTRAL_HANDOFF.rest"
    "R30_MATCHING_JACOBIAN.card"
    "R30_LATTICE_POTENTIAL.card"
    "R30_COORDINATE_COVER.card"
    "R30_REJECTED_FOIL.lean"
    "R30_GENERATED_PLURAL_REDERIVATION.lean")
  string(FIND "${opened}" "${required_open}" location)
  if(location EQUAL -1)
    message(FATAL_ERROR "R30 source-access log omits ${required_open}")
  endif()
endforeach()
foreach(forbidden IN ITEMS "/research/" "/reference/" "/papers/" "/evidence/"
    "/canon/" "/blueprint/" "ten-proofs" "laboratory")
  string(FIND "${opened}" "${forbidden}" location)
  if(NOT location EQUAL -1)
    message(FATAL_ERROR "R30 source-access log opened forbidden material: ${forbidden}")
  endif()
endforeach()
string(REGEX MATCHALL "\n" opened_lines "${opened}")
list(LENGTH opened_lines open_count)
file(SHA256 "${LOG}" log_sha256)
file(WRITE "${OUTPUT}"
  "truth_status=established-bounded\n"
  "evidence=implemented-exact\n"
  "instrument=LD_PRELOAD open/open64/openat/openat64 syscall witness\n"
  "instrumented_deed_exit=${deed_result}\n"
  "opened_path_occurrences=${open_count}\n"
  "opened_path_log_sha256=${log_sha256}\n"
  "required_runtime_sources=R29_rest,three_R30_cards,foil_and_valid_checker_faces\n"
  "forbidden_repository_sources=absent\n"
  "released_pdf=absent\n"
  "laboratory_material=absent\n")
