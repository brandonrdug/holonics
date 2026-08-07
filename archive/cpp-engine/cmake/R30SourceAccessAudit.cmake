cmake_minimum_required(VERSION 4.3.2 FATAL_ERROR)
set(holonic_required EXECUTABLE PROBE LOG OUTPUT SOURCE_ROOT DEED PREDECESSOR HANDOFF
    MATCHING LATTICE COVER SOURCE OLEAN STDOUT STDERR FOIL_SOURCE FOIL_OLEAN FOIL_STDOUT
    FOIL_STDERR FORMAL_ROOT TOOLCHAIN MANIFEST ARTIFACT_ROOT ATLAS DOSSIER)
foreach(required IN LISTS holonic_required)
  if(NOT DEFINED ${required})
    message(FATAL_ERROR "R30 source-access audit requires ${required}")
  endif()
endforeach()

# The audit re-executes the deeds under a probe to observe what they open. Those
# runs must NOT land on the standing. Writing the deeds' own output paths from
# here is an undeclared write: it gives every founding downstream of this one an
# input newer than its output, so the whole chain is dirty again the moment the
# audit finishes, forever. Measured before this was fixed: three consecutive
# twenty-two-minute passes that each re-founded thirty-odd deeds and converged on
# nothing.
#
# Everything the deeds write is redirected into a scratch region. Basenames are
# preserved, so every open-path check below still reads the same names, and the
# upstream rest and the cards are untouched because the deeds must genuinely read
# those.
get_filename_component(holonic_build_root "${ARTIFACT_ROOT}" DIRECTORY)
set(holonic_scratch "${ARTIFACT_ROOT}/r30-source-audit")
file(REMOVE_RECURSE "${holonic_scratch}")
file(MAKE_DIRECTORY "${holonic_scratch}")
foreach(holonic_key IN LISTS holonic_required)
  if(NOT holonic_key MATCHES
      "^(OUTPUT|ARTIFACT_ROOT|SOURCE_ROOT|PROBE|EXECUTABLE|PREDECESSOR|LOG|R[0-9]+_REST)$"
      AND NOT holonic_key MATCHES "_LOG$|_EXEC$"
      AND "${${holonic_key}}" MATCHES "^${holonic_build_root}/")
    get_filename_component(holonic_base "${${holonic_key}}" NAME)
    set(${holonic_key} "${holonic_scratch}/${holonic_base}")
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
