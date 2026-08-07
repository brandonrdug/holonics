# The deposited standing is evidence only if something can check it.
#
# `standing/MANIFEST.txt` binds every deposited return to two hashes: the
# content it holds, and the closure that founded it — the deed binary together
# with every card and rest it mounted. Until now nothing read either. A manifest
# no reader consumes is the same defect as the laboratory's seven per-run TSVs,
# written by the deed and read by nothing, which is why analysing a figure there
# meant re-deriving nine thousand rows by hand.
#
# Two failures are distinguished, and the distinction is the whole point:
#
#   CONTENT drift  — a deposited file no longer matches its recorded hash.
#                    The deposit is corrupt. This REFUSES.
#
#   CLOSURE drift  — the founding's inputs have moved since the deposit.
#                    The machine has advanced past what it rested. This is
#                    ordinary and is REPORTED, never refused: a standing that
#                    could not fall behind the current would not be standing.

foreach(required IN ITEMS STANDING BUILD_ROOT OUTPUT)
  if(NOT DEFINED ${required})
    message(FATAL_ERROR "holonic registry requires ${required}")
  endif()
endforeach()

set(manifest "${STANDING}/MANIFEST.txt")
if(NOT EXISTS "${manifest}")
  message(FATAL_ERROR "registry: no deposited standing at ${manifest}")
endif()

file(STRINGS "${manifest}" lines)
set(checked 0)
set(absent 0)
set(content_drift 0)
set(closure_drift 0)
set(closure_held 0)
set(report "")

foreach(line IN LISTS lines)
  if(NOT line MATCHES "^([^ ]+) ([0-9a-f]+) ([0-9a-f]+) (.+)$")
    continue()
  endif()
  set(relative "${CMAKE_MATCH_1}")
  set(recorded_content "${CMAKE_MATCH_2}")
  set(recorded_closure "${CMAKE_MATCH_3}")
  set(founding "${CMAKE_MATCH_4}")
  math(EXPR checked "${checked}+1")

  set(deposited "${STANDING}/${relative}")
  if(NOT EXISTS "${deposited}")
    math(EXPR absent "${absent}+1")
    string(APPEND report "absent ${relative} ${founding}\n")
    continue()
  endif()
  file(SHA256 "${deposited}" holds)
  if(NOT holds STREQUAL recorded_content)
    math(EXPR content_drift "${content_drift}+1")
    string(APPEND report "content_drift ${relative} ${founding}\n")
    continue()
  endif()

  # Does the founding still return this? The build tree carries the current
  # answer; the standing carries the rested one. They may honestly differ.
  set(current "${BUILD_ROOT}/${relative}")
  if(EXISTS "${current}")
    file(SHA256 "${current}" now)
    if(now STREQUAL recorded_content)
      math(EXPR closure_held "${closure_held}+1")
    else()
      math(EXPR closure_drift "${closure_drift}+1")
      string(APPEND report "closure_drift ${relative} ${founding}\n")
    endif()
  endif()
endforeach()

file(WRITE "${OUTPUT}"
  "truth_status=established-bounded\n"
  "evidence=computational-witness\n"
  "law=a deposit is evidence only where its content hash still holds\n"
  "checked=${checked}\n"
  "content_drift=${content_drift}\n"
  "absent=${absent}\n"
  "closure_held=${closure_held}\n"
  "closure_drift=${closure_drift}\n"
  "${report}")

if(content_drift GREATER 0 OR absent GREATER 0)
  message(FATAL_ERROR
    "registry: ${content_drift} deposited returns no longer match their "
    "recorded content and ${absent} are absent; see ${OUTPUT}")
endif()
message(STATUS
  "registry: ${checked} deposits hold; ${closure_held} still current, "
  "${closure_drift} superseded by the build tree")
