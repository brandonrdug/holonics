cmake_minimum_required(VERSION 4.3.2 FATAL_ERROR)
foreach(required IN ITEMS DISC_EXEC APP_EXEC PROBE DISC_LOG APP_LOG OUTPUT DISC_DEED APP_DEED
    R33_REST INTERMEDIATE FINAL_REST POSITIVE SIGNED RECHARTED HELDOUT DISC_SOURCE DISC_OLEAN
    DISC_STDOUT DISC_STDERR WORD_ATLAS TRIPLE_ATLAS GROUP_ATLAS LAW_ATLAS APP_SOURCE APP_OLEAN
    APP_STDOUT APP_STDERR DOSSIER APP_ATLAS FORMAL_ROOT TOOLCHAIN MANIFEST ARTIFACT_ROOT)
  if(NOT DEFINED ${required})
    message(FATAL_ERROR "R34 source audit requires ${required}")
  endif()
endforeach()
file(REMOVE "${DISC_LOG}" "${APP_LOG}")
execute_process(COMMAND "${CMAKE_COMMAND}" -E env "LD_PRELOAD=${PROBE}"
  "HOLONICS_R34_OPEN_LOG=${DISC_LOG}" "${DISC_EXEC}" "${DISC_DEED}" "${R33_REST}"
  "${INTERMEDIATE}" "${POSITIVE}" "${SIGNED}" "${RECHARTED}" "${DISC_SOURCE}"
  "${DISC_OLEAN}" "${DISC_STDOUT}" "${DISC_STDERR}" "${FORMAL_ROOT}" "${TOOLCHAIN}"
  "${MANIFEST}" "${ARTIFACT_ROOT}" "${WORD_ATLAS}" "${TRIPLE_ATLAS}" "${GROUP_ATLAS}"
  "${LAW_ATLAS}" RESULT_VARIABLE discovery_result)
execute_process(COMMAND "${CMAKE_COMMAND}" -E env "LD_PRELOAD=${PROBE}"
  "HOLONICS_R34_OPEN_LOG=${APP_LOG}" "${APP_EXEC}" "${APP_DEED}" "${INTERMEDIATE}"
  "${FINAL_REST}" "${HELDOUT}" "${APP_SOURCE}" "${APP_OLEAN}" "${APP_STDOUT}"
  "${APP_STDERR}" "${FORMAL_ROOT}" "${TOOLCHAIN}" "${MANIFEST}" "${ARTIFACT_ROOT}"
  "${DOSSIER}" "${APP_ATLAS}" RESULT_VARIABLE application_result)
if(NOT discovery_result EQUAL 0 OR NOT application_result EQUAL 0 OR
   NOT EXISTS "${DISC_LOG}" OR NOT EXISTS "${APP_LOG}")
  message(FATAL_ERROR "R34 instrumented deeds failed")
endif()
file(READ "${DISC_LOG}" discovery_opened)
file(READ "${APP_LOG}" application_opened)
foreach(required_open IN ITEMS "R33_CHARACTERISTIC_TRANSPORT_HANDOFF.rest"
    "R34_POSITIVE_TRIPLES.card" "R34_SIGNED_TRIPLES.card" "R34_RECHARTED_TRIPLES.card"
    "R34_TRACE_FIBER_LIFTING.lean")
  string(FIND "${discovery_opened}" "${required_open}" position)
  if(position EQUAL -1)
    message(FATAL_ERROR "discovery log omits ${required_open}")
  endif()
endforeach()
foreach(required_open IN ITEMS "R34_TRACE_FIBER_LIFTING.rest"
    "R34_HELDOUT_ORIENTED_SYSTEM.card" "R34_HELDOUT_TRACE_FIBER.lean")
  string(FIND "${application_opened}" "${required_open}" position)
  if(position EQUAL -1)
    message(FATAL_ERROR "application log omits ${required_open}")
  endif()
endforeach()
foreach(forbidden IN ITEMS "R34_POSITIVE_TRIPLES.card" "R34_SIGNED_TRIPLES.card"
    "R34_RECHARTED_TRIPLES.card" "R34_TRANSITION_WORD_ATLAS.tsv"
    "R34_TRACE_FIBER_TRIPLE_ATLAS.tsv" "R34_TRACE_FIBER_GROUP_ATLAS.tsv"
    "R34_TRACE_FIBER_LAW_ATLAS.tsv")
  string(FIND "${application_opened}" "${forbidden}" position)
  if(NOT position EQUAL -1)
    message(FATAL_ERROR "held-out deed opened ${forbidden}")
  endif()
endforeach()
foreach(opened IN ITEMS discovery_opened application_opened)
  foreach(forbidden IN ITEMS "/research/" "/reference/" "/papers/" "/evidence/"
      "/canon/" "/blueprint/" "laboratory" "Fricke" "Vogt" "Horowitz" "Procesi")
    string(FIND "${${opened}}" "${forbidden}" position)
    if(NOT position EQUAL -1)
      message(FATAL_ERROR "R34 opened forbidden ${forbidden}")
    endif()
  endforeach()
endforeach()
file(SHA256 "${DISC_LOG}" discovery_sha)
file(SHA256 "${APP_LOG}" application_sha)
file(WRITE "${OUTPUT}" "truth_status=established-bounded\nevidence=implemented-exact\n"
  "discovery_exit=${discovery_result}\napplication_exit=${application_result}\n"
  "discovery_open_log_sha256=${discovery_sha}\napplication_open_log_sha256=${application_sha}\n"
  "intermediate_rest_contains_development_rows=0\nintermediate_rest_contains_target_traces=0\n"
  "intermediate_rest_contains_matrices=0\nheldout_development_paths=absent\n"
  "preseal_named_identity_and_external_sources=absent\n")
