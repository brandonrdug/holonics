cmake_minimum_required(VERSION 4.3.2 FATAL_ERROR)
foreach(required IN ITEMS CULT_EXEC APP_EXEC TMP R30_REST D0 D1 D2 D3 H0 H1 H2 H3
    FORMAL_ROOT TOOLCHAIN MANIFEST ARTIFACT_ROOT CULT_DEED APP_DEED INTERMEDIATE FINAL_REST
    CULT_SOURCE CULT_OLEAN CULT_STDOUT CULT_STDERR CULT_ATLAS APP_SOURCE APP_OLEAN
    APP_STDOUT APP_STDERR DOSSIER APP_ATLAS OUTPUT)
  if(NOT DEFINED ${required})
    message(FATAL_ERROR "R31 determinism requires ${required}")
  endif()
endforeach()
file(REMOVE_RECURSE "${TMP}")
file(MAKE_DIRECTORY "${TMP}")
set(cult_deed "${TMP}/cultivation.txt")
set(intermediate "${TMP}/organs.rest")
set(cult_source "${TMP}/cultivation.lean")
set(cult_olean "${TMP}/cultivation.olean")
set(cult_stdout "${TMP}/cultivation.stdout")
set(cult_stderr "${TMP}/cultivation.stderr")
set(cult_atlas "${TMP}/cultivation.tsv")
set(app_deed "${TMP}/application.txt")
set(final_rest "${TMP}/application.rest")
set(app_source "${TMP}/application.lean")
set(app_olean "${TMP}/application.olean")
set(app_stdout "${TMP}/application.stdout")
set(app_stderr "${TMP}/application.stderr")
set(dossier "${TMP}/dossier.md")
set(app_atlas "${TMP}/application.tsv")
execute_process(COMMAND "${CULT_EXEC}" "${cult_deed}" "${R30_REST}" "${intermediate}"
  "${D0}" "${D1}" "${D2}" "${D3}" "${cult_source}" "${cult_olean}"
  "${cult_stdout}" "${cult_stderr}" "${FORMAL_ROOT}" "${TOOLCHAIN}" "${MANIFEST}"
  "${ARTIFACT_ROOT}" "${cult_atlas}" RESULT_VARIABLE cultivation_result)
execute_process(COMMAND "${APP_EXEC}" "${app_deed}" "${intermediate}" "${final_rest}"
  "${H0}" "${H1}" "${H2}" "${H3}" "${app_source}" "${app_olean}"
  "${app_stdout}" "${app_stderr}" "${FORMAL_ROOT}" "${TOOLCHAIN}" "${MANIFEST}"
  "${ARTIFACT_ROOT}" "${dossier}" "${app_atlas}" RESULT_VARIABLE application_result)
if(NOT cultivation_result EQUAL 0 OR NOT application_result EQUAL 0)
  message(FATAL_ERROR "R31 deterministic replay deed failed")
endif()
set(baseline "${CULT_DEED}" "${INTERMEDIATE}" "${CULT_SOURCE}" "${CULT_STDOUT}"
  "${CULT_STDERR}" "${CULT_ATLAS}" "${APP_DEED}" "${FINAL_REST}" "${APP_SOURCE}"
  "${APP_STDOUT}" "${APP_STDERR}" "${DOSSIER}" "${APP_ATLAS}")
set(replay "${cult_deed}" "${intermediate}" "${cult_source}" "${cult_stdout}"
  "${cult_stderr}" "${cult_atlas}" "${app_deed}" "${final_rest}" "${app_source}"
  "${app_stdout}" "${app_stderr}" "${dossier}" "${app_atlas}")
list(LENGTH baseline count)
math(EXPR last "${count} - 1")
foreach(index RANGE 0 ${last})
  list(GET baseline ${index} left)
  list(GET replay ${index} right)
  execute_process(COMMAND "${CMAKE_COMMAND}" -E compare_files "${left}" "${right}"
    RESULT_VARIABLE difference)
  if(NOT difference EQUAL 0)
    message(FATAL_ERROR "R31 deterministic replay differs at ${left}")
  endif()
endforeach()
file(WRITE "${OUTPUT}" "truth_status=established-bounded\nevidence=implemented-exact\n"
  "cultivation_replay_exit=${cultivation_result}\napplication_replay_exit=${application_result}\n"
  "byte_identical_artifacts=${count}\ndeterministic=1\n")
