cmake_minimum_required(VERSION 4.3.2 FATAL_ERROR)
foreach(required IN ITEMS CULT_EXEC APP_EXEC PROBE CULT_LOG APP_LOG OUTPUT CULT_DEED APP_DEED
    R30_REST INTERMEDIATE FINAL_REST D0 D1 D2 D3 H0 H1 H2 H3 CULT_SOURCE CULT_OLEAN
    CULT_STDOUT CULT_STDERR CULT_ATLAS APP_SOURCE APP_OLEAN APP_STDOUT APP_STDERR DOSSIER
    APP_ATLAS FORMAL_ROOT TOOLCHAIN MANIFEST ARTIFACT_ROOT)
  if(NOT DEFINED ${required})
    message(FATAL_ERROR "R31 source audit requires ${required}")
  endif()
endforeach()
file(REMOVE "${CULT_LOG}" "${APP_LOG}")
execute_process(COMMAND "${CMAKE_COMMAND}" -E env "LD_PRELOAD=${PROBE}"
  "HOLONICS_R31_OPEN_LOG=${CULT_LOG}" "${CULT_EXEC}" "${CULT_DEED}" "${R30_REST}"
  "${INTERMEDIATE}" "${D0}" "${D1}" "${D2}" "${D3}" "${CULT_SOURCE}" "${CULT_OLEAN}"
  "${CULT_STDOUT}" "${CULT_STDERR}" "${FORMAL_ROOT}" "${TOOLCHAIN}" "${MANIFEST}"
  "${ARTIFACT_ROOT}" "${CULT_ATLAS}" RESULT_VARIABLE cultivation_result)
execute_process(COMMAND "${CMAKE_COMMAND}" -E env "LD_PRELOAD=${PROBE}"
  "HOLONICS_R31_OPEN_LOG=${APP_LOG}" "${APP_EXEC}" "${APP_DEED}" "${INTERMEDIATE}"
  "${FINAL_REST}" "${H0}" "${H1}" "${H2}" "${H3}" "${APP_SOURCE}" "${APP_OLEAN}"
  "${APP_STDOUT}" "${APP_STDERR}" "${FORMAL_ROOT}" "${TOOLCHAIN}" "${MANIFEST}"
  "${ARTIFACT_ROOT}" "${DOSSIER}" "${APP_ATLAS}" RESULT_VARIABLE application_result)
if(NOT cultivation_result EQUAL 0 OR NOT application_result EQUAL 0 OR
   NOT EXISTS "${CULT_LOG}" OR NOT EXISTS "${APP_LOG}")
  message(FATAL_ERROR "R31 instrumented deeds failed")
endif()
file(READ "${CULT_LOG}" cultivation_opened)
file(READ "${APP_LOG}" application_opened)
foreach(required_open IN ITEMS "R30_PLURAL_REDERIVATION_HANDOFF.rest" "R31_R18_RECIPROCAL.card"
    "R31_R24_CENTRAL_WALK.card" "R31_R29_SIGNED_TRACE.card" "R31_R30_POLYGONS.card"
    "R31_CULTIVATED_ORGANS.lean")
  string(FIND "${cultivation_opened}" "${required_open}" position)
  if(position EQUAL -1)
    message(FATAL_ERROR "cultivation log omits ${required_open}")
  endif()
endforeach()
foreach(required_open IN ITEMS "R31_CULTIVATED_ORGANS.rest" "R31_CONDUCTANCE_STAR.card"
    "R31_SQUARE_WALK.card" "R31_SIGNED_CARRIER.card" "R31_GRADED_INCIDENCE.card"
    "R31_ORGAN_TRANSPORT.lean")
  string(FIND "${application_opened}" "${required_open}" position)
  if(position EQUAL -1)
    message(FATAL_ERROR "application log omits ${required_open}")
  endif()
endforeach()
foreach(forbidden IN ITEMS "R31_R18_RECIPROCAL.card" "R31_R24_CENTRAL_WALK.card"
    "R31_R29_SIGNED_TRACE.card" "R31_R30_POLYGONS.card" "R31_CULTIVATION_ATLAS.tsv")
  string(FIND "${application_opened}" "${forbidden}" position)
  if(NOT position EQUAL -1)
    message(FATAL_ERROR "held-out deed opened ${forbidden}")
  endif()
endforeach()
foreach(opened IN ITEMS cultivation_opened application_opened)
  foreach(forbidden IN ITEMS "/research/" "/reference/" "/papers/" "/evidence/"
      "/canon/" "/blueprint/" "ten-proofs" "laboratory")
    string(FIND "${${opened}}" "${forbidden}" position)
    if(NOT position EQUAL -1)
      message(FATAL_ERROR "R31 opened forbidden ${forbidden}")
    endif()
  endforeach()
endforeach()
file(SHA256 "${CULT_LOG}" cultivation_sha)
file(SHA256 "${APP_LOG}" application_sha)
file(WRITE "${OUTPUT}" "truth_status=established-bounded\nevidence=implemented-exact\n"
  "cultivation_exit=${cultivation_result}\napplication_exit=${application_result}\n"
  "cultivation_open_log_sha256=${cultivation_sha}\napplication_open_log_sha256=${application_sha}\n"
  "intermediate_rest_contains_samples=0\nheldout_development_paths=absent\n"
  "research_reference_papers_evidence_canon_blueprint=absent\n")
