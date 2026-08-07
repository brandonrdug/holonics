cmake_minimum_required(VERSION 4.3.2 FATAL_ERROR)
foreach(required IN ITEMS DISC_EXEC APP_EXEC TMP R32_REST POSITIVE SIGNED RECHARTED HELDOUT
    FORMAL_ROOT TOOLCHAIN MANIFEST ARTIFACT_ROOT DISC_DEED APP_DEED INTERMEDIATE FINAL_REST
    DISC_SOURCE DISC_STDOUT DISC_STDERR WORD_ATLAS PAIR_ATLAS GROUP_ATLAS LAW_ATLAS APP_SOURCE
    APP_STDOUT APP_STDERR DOSSIER APP_ATLAS OUTPUT)
  if(NOT DEFINED ${required})
    message(FATAL_ERROR "R33 determinism requires ${required}")
  endif()
endforeach()
file(REMOVE_RECURSE "${TMP}")
file(MAKE_DIRECTORY "${TMP}")
set(disc_deed "${TMP}/discovery.txt")
set(intermediate "${TMP}/characteristic.rest")
set(disc_source "${TMP}/R33_CHARACTERISTIC_HYPERGEOMETRY.lean")
set(disc_olean "${TMP}/R33_CHARACTERISTIC_HYPERGEOMETRY.olean")
set(disc_stdout "${TMP}/discovery.stdout")
set(disc_stderr "${TMP}/discovery.stderr")
set(word_atlas "${TMP}/words.tsv")
set(pair_atlas "${TMP}/pairs.tsv")
set(group_atlas "${TMP}/groups.tsv")
set(law_atlas "${TMP}/law.tsv")
set(app_deed "${TMP}/application.txt")
set(final_rest "${TMP}/application.rest")
set(app_source "${TMP}/R33_HELDOUT_CHARACTERISTIC.lean")
set(app_olean "${TMP}/R33_HELDOUT_CHARACTERISTIC.olean")
set(app_stdout "${TMP}/application.stdout")
set(app_stderr "${TMP}/application.stderr")
set(dossier "${TMP}/dossier.md")
set(app_atlas "${TMP}/application.tsv")
execute_process(COMMAND "${DISC_EXEC}" "${disc_deed}" "${R32_REST}" "${intermediate}"
  "${POSITIVE}" "${SIGNED}" "${RECHARTED}" "${disc_source}" "${disc_olean}"
  "${disc_stdout}" "${disc_stderr}" "${FORMAL_ROOT}" "${TOOLCHAIN}" "${MANIFEST}"
  "${ARTIFACT_ROOT}" "${word_atlas}" "${pair_atlas}" "${group_atlas}" "${law_atlas}"
  RESULT_VARIABLE discovery_result)
execute_process(COMMAND "${APP_EXEC}" "${app_deed}" "${intermediate}" "${final_rest}"
  "${HELDOUT}" "${app_source}" "${app_olean}" "${app_stdout}" "${app_stderr}"
  "${FORMAL_ROOT}" "${TOOLCHAIN}" "${MANIFEST}" "${ARTIFACT_ROOT}" "${dossier}"
  "${app_atlas}" RESULT_VARIABLE application_result)
if(NOT discovery_result EQUAL 0 OR NOT application_result EQUAL 0)
  message(FATAL_ERROR "R33 deterministic replay deed failed")
endif()
set(baseline "${DISC_DEED}" "${INTERMEDIATE}" "${DISC_SOURCE}" "${DISC_STDOUT}"
  "${DISC_STDERR}" "${WORD_ATLAS}" "${PAIR_ATLAS}" "${GROUP_ATLAS}" "${LAW_ATLAS}"
  "${APP_DEED}" "${FINAL_REST}" "${APP_SOURCE}" "${APP_STDOUT}" "${APP_STDERR}"
  "${DOSSIER}" "${APP_ATLAS}")
set(replay "${disc_deed}" "${intermediate}" "${disc_source}" "${disc_stdout}"
  "${disc_stderr}" "${word_atlas}" "${pair_atlas}" "${group_atlas}" "${law_atlas}"
  "${app_deed}" "${final_rest}" "${app_source}" "${app_stdout}" "${app_stderr}"
  "${dossier}" "${app_atlas}")
list(LENGTH baseline count)
math(EXPR last "${count}-1")
foreach(index RANGE 0 ${last})
  list(GET baseline ${index} left)
  list(GET replay ${index} right)
  execute_process(COMMAND "${CMAKE_COMMAND}" -E compare_files "${left}" "${right}"
    RESULT_VARIABLE difference)
  if(NOT difference EQUAL 0)
    message(FATAL_ERROR "R33 deterministic replay differs at ${left}")
  endif()
endforeach()
file(WRITE "${OUTPUT}" "truth_status=established-bounded\nevidence=implemented-exact\n"
  "discovery_replay_exit=${discovery_result}\napplication_replay_exit=${application_result}\n"
  "byte_identical_artifacts=${count}\ndeterministic=1\n")
