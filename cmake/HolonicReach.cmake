cmake_minimum_required(VERSION 4.3.2 FATAL_ERROR)

# The reach audit.
#
# Every receipt in this repository is true and every one is local. The grade
# asks *did this deed return* and never *does the body conduct through it*. A
# mechanism at one percent reach earns the same grade as one at a hundred, so
# the two-body split of 2026-08 stood for thirty-five construction steps without
# a single receipt disagreeing with itself.
#
# This audit computes, over the actual include graph, how much of the body each
# spine mechanism reaches, and writes it beside the build. It fails only on a
# regression against the recorded floor -- reach is a number the record must
# carry, not a target to hit by widening includes.

if(NOT DEFINED SCAN_ROOT OR NOT DEFINED OUTPUT)
  message(FATAL_ERROR "reach audit requires SCAN_ROOT and OUTPUT")
endif()

file(GLOB_RECURSE reach_headers LIST_DIRECTORIES false
  "${SCAN_ROOT}/include/holonics/*.hpp" "${SCAN_ROOT}/include/holonics/*.cuh")
list(LENGTH reach_headers reach_total)
if(reach_total EQUAL 0)
  message(FATAL_ERROR "reach audit found no headers under ${SCAN_ROOT}")
endif()

# Build the reverse include edges once.
foreach(path IN LISTS reach_headers)
  file(STRINGS "${path}" lines REGEX "^#[ \t]*include[ \t]*<holonics/")
  foreach(line IN LISTS lines)
    string(REGEX REPLACE ".*<holonics/([^>]+)>.*" "\\1" target "${line}")
    set(edge "${SCAN_ROOT}/include/holonics/${target}")
    list(APPEND reach_from_${edge} "${path}")
  endforeach()
endforeach()

function(holonics_reach seed out_count)
  set(seen "${seed}")
  set(stack "${seed}")
  while(stack)
    list(POP_BACK stack current)
    foreach(dependent IN LISTS reach_from_${current})
      if(NOT dependent IN_LIST seen)
        list(APPEND seen "${dependent}")
        list(APPEND stack "${dependent}")
      endif()
    endforeach()
  endwhile()
  list(LENGTH seen counted)
  set(${out_count} "${counted}" PARENT_SCOPE)
endfunction()

# The spine, named. These are the mechanisms the doctrine says the body conducts
# through; their reach is the honest measure of whether it does.
set(reach_seeds
    "body/swing.hpp"
    "structure/chi_pair.hpp"
    "structure/local_transport.hpp"
    "structure/transition_invariants.hpp"
    "body/live_machine.hpp"
    "body/continuing_body.hpp"
    "current/information_receipt.hpp"
    "exact/small_rational.hpp")

# Floors and ceilings, measured 2026-08-06.
#
# A spine mechanism carries a FLOOR: the body must not conduct through less of
# it than it already does. A carrier under supersession carries a CEILING: it
# must not spread further while it is being retired. `continuing_body` fell from
# 169 to 145 in the cut of 2026-08-06 and that fall is the work, not a
# regression -- which the first version of this audit could not express.
set(reach_floor_body/swing.hpp 9)
set(reach_floor_structure/chi_pair.hpp 13)
set(reach_floor_structure/local_transport.hpp 13)
set(reach_floor_structure/transition_invariants.hpp 9)
set(reach_floor_body/live_machine.hpp 8)
set(reach_floor_current/information_receipt.hpp 1)
set(reach_floor_exact/small_rational.hpp 1)

set(reach_ceiling_body/continuing_body.hpp 145)

set(report "headers_total=${reach_total}\n")
set(regressions "")
foreach(seed IN LISTS reach_seeds)
  set(path "${SCAN_ROOT}/include/holonics/${seed}")
  if(NOT EXISTS "${path}")
    message(FATAL_ERROR "reach audit: declared spine header is absent: ${seed}")
  endif()
  holonics_reach("${path}" counted)
  math(EXPR permille "${counted} * 1000 / ${reach_total}")
  string(APPEND report "reach ${seed} = ${counted}/${reach_total} (${permille} per mille)\n")
  set(floor "${reach_floor_${seed}}")
  if(NOT floor STREQUAL "" AND counted LESS floor)
    string(APPEND regressions "  ${seed}: ${counted} < recorded floor ${floor}\n")
  endif()
  set(ceiling "${reach_ceiling_${seed}}")
  if(NOT ceiling STREQUAL "" AND counted GREATER ceiling)
    string(APPEND regressions
      "  ${seed}: ${counted} > recorded ceiling ${ceiling} -- a superseded carrier spread\n")
  endif()
endforeach()

file(WRITE "${OUTPUT}" "truth_status=established-bounded\nevidence=computational-witness\n"
  "law=a mechanism is admitted at the reach it conducts through\n${report}")

if(NOT regressions STREQUAL "")
  message(FATAL_ERROR "reach audit failed:\n${regressions}")
endif()
message(STATUS "reach audit: ${reach_total} headers")
