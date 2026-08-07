cmake_minimum_required(VERSION 4.3.2 FATAL_ERROR)
if(NOT DEFINED OUTPUT)
  message(FATAL_ERROR "R31 seal requires OUTPUT")
endif()
foreach(required IN ITEMS SOURCE_AUDIT CULT_DEED APP_DEED INTERMEDIATE FINAL_REST
    CULT_SOURCE CULT_OLEAN CULT_ATLAS APP_SOURCE APP_OLEAN DOSSIER APP_ATLAS DETERMINISM)
  if(NOT DEFINED ${required} OR NOT EXISTS "${${required}}")
    message(FATAL_ERROR "R31 seal requires ${required}")
  endif()
endforeach()
set(paths "${SOURCE_AUDIT}" "${CULT_DEED}" "${APP_DEED}" "${INTERMEDIATE}"
  "${FINAL_REST}" "${CULT_SOURCE}" "${CULT_OLEAN}" "${CULT_ATLAS}"
  "${APP_SOURCE}" "${APP_OLEAN}" "${DOSSIER}" "${APP_ATLAS}")
list(APPEND paths "${DETERMINISM}")
set(manifest "")
foreach(path IN LISTS paths)
  file(SHA256 "${path}" digest)
  get_filename_component(name "${path}" NAME)
  string(APPEND manifest "${digest}  ${name}\n")
endforeach()
file(WRITE "${OUTPUT}" "truth_status=established-bounded\n"
  "evidence=implemented-exact,computational-witness\nsealed_artifacts_begin\n"
  "${manifest}sealed_artifacts_end\n")
