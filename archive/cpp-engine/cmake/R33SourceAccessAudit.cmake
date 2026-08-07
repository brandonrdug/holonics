cmake_minimum_required(VERSION 4.3.2 FATAL_ERROR)
set(holonic_required DISC_EXEC APP_EXEC PROBE DISC_LOG APP_LOG OUTPUT DISC_DEED APP_DEED
    R32_REST INTERMEDIATE FINAL_REST POSITIVE SIGNED RECHARTED HELDOUT DISC_SOURCE DISC_OLEAN
    DISC_STDOUT DISC_STDERR WORD_ATLAS PAIR_ATLAS GROUP_ATLAS LAW_ATLAS APP_SOURCE APP_OLEAN
    APP_STDOUT APP_STDERR DOSSIER APP_ATLAS FORMAL_ROOT TOOLCHAIN MANIFEST ARTIFACT_ROOT)
foreach(required IN LISTS holonic_required)
  if(NOT DEFINED ${required})
    message(FATAL_ERROR "R33 source audit requires ${required}")
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
set(holonic_scratch "${ARTIFACT_ROOT}/r33-source-audit")
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
file(REMOVE "${DISC_LOG}" "${APP_LOG}")
execute_process(COMMAND "${CMAKE_COMMAND}" -E env "LD_PRELOAD=${PROBE}"
  "HOLONICS_R33_OPEN_LOG=${DISC_LOG}" "${DISC_EXEC}" "${DISC_DEED}" "${R32_REST}"
  "${INTERMEDIATE}" "${POSITIVE}" "${SIGNED}" "${RECHARTED}" "${DISC_SOURCE}"
  "${DISC_OLEAN}" "${DISC_STDOUT}" "${DISC_STDERR}" "${FORMAL_ROOT}" "${TOOLCHAIN}"
  "${MANIFEST}" "${ARTIFACT_ROOT}" "${WORD_ATLAS}" "${PAIR_ATLAS}" "${GROUP_ATLAS}"
  "${LAW_ATLAS}" RESULT_VARIABLE discovery_result)
execute_process(COMMAND "${CMAKE_COMMAND}" -E env "LD_PRELOAD=${PROBE}"
  "HOLONICS_R33_OPEN_LOG=${APP_LOG}" "${APP_EXEC}" "${APP_DEED}" "${INTERMEDIATE}"
  "${FINAL_REST}" "${HELDOUT}" "${APP_SOURCE}" "${APP_OLEAN}" "${APP_STDOUT}"
  "${APP_STDERR}" "${FORMAL_ROOT}" "${TOOLCHAIN}" "${MANIFEST}" "${ARTIFACT_ROOT}"
  "${DOSSIER}" "${APP_ATLAS}" RESULT_VARIABLE application_result)
if(NOT discovery_result EQUAL 0 OR NOT application_result EQUAL 0 OR
   NOT EXISTS "${DISC_LOG}" OR NOT EXISTS "${APP_LOG}")
  message(FATAL_ERROR "R33 instrumented deeds failed")
endif()
file(READ "${DISC_LOG}" discovery_opened)
file(READ "${APP_LOG}" application_opened)
foreach(required_open IN ITEMS "R32_SELF_DERIVATION_HANDOFF.rest" "R33_POSITIVE_TRANSITIONS.card"
    "R33_SIGNED_TRANSITIONS.card" "R33_RECHARTED_TRANSITIONS.card"
    "R33_CHARACTERISTIC_HYPERGEOMETRY.lean")
  string(FIND "${discovery_opened}" "${required_open}" position)
  if(position EQUAL -1)
    message(FATAL_ERROR "discovery log omits ${required_open}")
  endif()
endforeach()
foreach(required_open IN ITEMS "R33_CHARACTERISTIC_HYPERGEOMETRY.rest"
    "R33_HELDOUT_LOCAL_SYSTEM.card" "R33_HELDOUT_CHARACTERISTIC.lean")
  string(FIND "${application_opened}" "${required_open}" position)
  if(position EQUAL -1)
    message(FATAL_ERROR "application log omits ${required_open}")
  endif()
endforeach()
foreach(forbidden IN ITEMS "R33_POSITIVE_TRANSITIONS.card" "R33_SIGNED_TRANSITIONS.card"
    "R33_RECHARTED_TRANSITIONS.card" "R33_TRANSITION_WORD_ATLAS.tsv"
    "R33_CHARACTERISTIC_PAIR_ATLAS.tsv" "R33_ARCHETYPE_GROUP_ATLAS.tsv"
    "R33_TRACE_LAW_ATLAS.tsv")
  string(FIND "${application_opened}" "${forbidden}" position)
  if(NOT position EQUAL -1)
    message(FATAL_ERROR "held-out deed opened ${forbidden}")
  endif()
endforeach()
foreach(opened IN ITEMS discovery_opened application_opened)
  foreach(forbidden IN ITEMS "/research/" "/reference/" "/papers/" "/evidence/"
      "/canon/" "/blueprint/" "laboratory" "Fricke" "Vogt")
    string(FIND "${${opened}}" "${forbidden}" position)
    if(NOT position EQUAL -1)
      message(FATAL_ERROR "R33 opened forbidden ${forbidden}")
    endif()
  endforeach()
endforeach()
file(SHA256 "${DISC_LOG}" discovery_sha)
file(SHA256 "${APP_LOG}" application_sha)
file(WRITE "${OUTPUT}" "truth_status=established-bounded\nevidence=implemented-exact\n"
  "discovery_exit=${discovery_result}\napplication_exit=${application_result}\n"
  "discovery_open_log_sha256=${discovery_sha}\napplication_open_log_sha256=${application_sha}\n"
  "intermediate_rest_contains_development_rows=0\nintermediate_rest_contains_matrices=0\n"
  "heldout_development_paths=absent\npreseal_named_identity_and_external_sources=absent\n")
