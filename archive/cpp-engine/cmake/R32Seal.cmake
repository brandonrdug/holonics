cmake_minimum_required(VERSION 4.3.2 FATAL_ERROR)
if(NOT DEFINED OUTPUT)
  message(FATAL_ERROR "R32 seal requires OUTPUT")
endif()
foreach(required IN ITEMS SOURCE_AUDIT DISC_DEED APP_DEED INTERMEDIATE FINAL_REST
    DISC_SOURCE DISC_OLEAN A0 A1 A2 A3 A4 A5 APP_SOURCE APP_OLEAN DOSSIER APP_ATLAS
    HOST_CONFORMANCE DETERMINISM)
  if(NOT DEFINED ${required} OR NOT EXISTS "${${required}}")
    message(FATAL_ERROR "R32 seal requires ${required}")
  endif()
endforeach()
set(paths "${SOURCE_AUDIT}" "${DISC_DEED}" "${APP_DEED}" "${INTERMEDIATE}" "${FINAL_REST}"
  "${DISC_SOURCE}" "${DISC_OLEAN}" "${A0}" "${A1}" "${A2}" "${A3}" "${A4}" "${A5}"
  "${APP_SOURCE}" "${APP_OLEAN}" "${DOSSIER}" "${APP_ATLAS}" "${HOST_CONFORMANCE}"
  "${DETERMINISM}")
set(manifest "")
foreach(path IN LISTS paths)
  file(SHA256 "${path}" digest)
  get_filename_component(name "${path}" NAME)
  string(APPEND manifest "${digest}  ${name}\n")
endforeach()
file(WRITE "${OUTPUT}" "truth_status=established-bounded\n"
  "evidence=implemented-exact,computational-witness\ncanon_opened_before_seal=0\n"
  "sealed_artifacts_begin\n${manifest}sealed_artifacts_end\n")
