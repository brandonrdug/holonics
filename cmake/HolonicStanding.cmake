# The founded return is standing. Re-deriving it is current.
#
# A deed is not a test. It is the machine running: it mounts a rest, contacts
# cards, computes on the card, and rests its return as a file. Registering that
# as `add_test` was a category error with a measured price. Measured 2026-08-07
# across 127 entries and roughly 2,250 serial seconds, about **1,320 of those
# seconds were byte-for-byte re-executions of a computation that had finished
# seconds earlier in the same invocation** — the trace-rebase chain ran its
# 527-second deed once as itself, again under the source-access probe, and a
# third time under the determinism replay, every single time anything at all was
# asked of any part of the tree.
#
# The deeds are already a dependency graph and always were: each one's rest is
# the next one's argument, written out longhand in the argument list. Nothing
# ever told the build graph that. `add_test` fires unconditionally, so the whole
# founded production was recomputed from zero to answer any question about any
# part of the repository.
#
# This module puts the deeds where they belong. The question *does this need to
# run* is answered by the input closure, not by the clock. A deed whose
# executable, cards, and mounted rest are unchanged does not run, because its
# return already stands.
#
# **Determinism is what licenses this.** The replay steps established that each
# deed is a pure function of its declared inputs, and the source-access audits
# established that it opens nothing outside them. Those two facts are exactly
# the certificate that the input closure is a complete cache key. They are
# properties of (executable, inputs), they are re-established whenever the
# executable or an input moves — which is what a build rule does — and repeating
# them on an unmoved closure could never add to them.

set_property(GLOBAL PROPERTY HOLONICS_STANDING_RETURNS "")
set_property(GLOBAL PROPERTY HOLONICS_CLAIMED_RETURNS "")
set_property(GLOBAL PROPERTY HOLONICS_NEVER_RETURNED "")

# Declares a path that no founding ever deposits, however many of them name it.
#
# The case this exists for is the **foil**: a proof the kernel is supposed to
# refuse, whose compiled object is therefore never produced. Its absence is the
# negative control, not work left undone. Declared as a return, it makes ninja
# chase a file whose non-existence is the point and re-run the founding — and
# everything downstream — on every invocation.
#
# It must be global rather than per-founding. Withholding it from the deed alone
# only hands the claim to the next founding that names it: the source-access
# audit, then the replay, then the seal. The same defect walks down the chain.
function(holonic_withhold)
  set_property(GLOBAL APPEND PROPERTY HOLONICS_NEVER_RETURNED ${ARGN})
endfunction()

# There is one card, so there is one founding at a time.
#
# ninja defaults to one job per core and would launch two dozen deeds at once
# against a single device. The first attempt did exactly that and the plural
# rederivation returned `executor_state=10` with `kernel_launches=0` and 7,194
# verification failures — a deed that never reached the card at all, reported as
# a mathematical failure. This is the same defect that made nineteen entries
# carry a two-times timeout margin against a measured cost: contention wearing
# the mask of a regression.
#
# The pool is depth one. The deeds are device-bound, so overlapping them buys
# nothing to trade against a false failure.
set_property(GLOBAL PROPERTY JOB_POOLS holonic_card=1)

# Where a founding may deposit. A path under one of these is material the
# machine produced; a path anywhere else is material it was handed.
set(HOLONICS_FOUNDING_REGIONS
  "${PROJECT_BINARY_DIR}/artifacts"
  "${PROJECT_BINARY_DIR}/receipts"
  "${PROJECT_BINARY_DIR}/generated")

# Sorts one argument into the returns, the mounts, the target dependencies, or
# none of them.
#
# An artifact path is a RETURN of the first founding that names it and a MOUNT
# for every founding after — which is precisely the lineage, read off the
# argument list, with no second declaration that could drift out of step with
# it. A path outside the artifact root that exists at configure time is a MOUNT:
# a card, a corpus, a toolchain file, a script. A `$<TARGET_FILE:x>` is a
# dependency on the target `x`.
function(_holonic_sort argument withheld returns_out mounts_out targets_out claimed_out)
  set(returns "${${returns_out}}")
  set(mounts "${${mounts_out}}")
  set(targets "${${targets_out}}")
  set(claimed "${${claimed_out}}")

  set(path "${argument}")
  if(path MATCHES "^-D([A-Za-z_0-9]+)=(.*)$")
    if(CMAKE_MATCH_1 IN_LIST withheld)
      return()
    endif()
    set(path "${CMAKE_MATCH_2}")
  elseif(path IN_LIST withheld)
    return()
  endif()

  get_property(never_returned GLOBAL PROPERTY HOLONICS_NEVER_RETURNED)
  if(path IN_LIST never_returned)
    return()
  endif()

  set(deposited FALSE)
  foreach(region IN LISTS HOLONICS_FOUNDING_REGIONS)
    if(path MATCHES "^${region}/")
      set(deposited TRUE)
      break()
    endif()
  endforeach()

  if(path MATCHES "\\$<TARGET_FILE:([A-Za-z_0-9]+)>")
    list(APPEND targets "${CMAKE_MATCH_1}")
  elseif(path IN_LIST HOLONICS_FOUNDING_REGIONS)
    # A founding region is a place, not a material.
  elseif(deposited)
    if(path IN_LIST claimed)
      list(APPEND mounts "${path}")
    else()
      # A founding may not deposit where an earlier founding already read. When
      # that happens the declaration order has inverted the dependency order,
      # and the graph would run the consumer first and silently hand it a stale
      # or absent input. R31's seal was declared above the determinism replay
      # whose receipt it reads, and ninja duly sealed before replaying.
      get_property(already_mounted GLOBAL PROPERTY HOLONICS_MOUNTED_PATHS)
      if(path IN_LIST already_mounted)
        message(FATAL_ERROR
          "founding deposits into ${path}, which an earlier founding mounts; "
          "declare the producer before the consumer")
      endif()
      list(APPEND returns "${path}")
      list(APPEND claimed "${path}")
    endif()
  elseif(IS_DIRECTORY "${path}")
    # A root handed over so the founding can reach material below it.
  elseif(EXISTS "${path}")
    list(APPEND mounts "${path}")
  endif()

  set(${returns_out} "${returns}" PARENT_SCOPE)
  set(${mounts_out} "${mounts}" PARENT_SCOPE)
  set(${targets_out} "${targets}" PARENT_SCOPE)
  set(${claimed_out} "${claimed}" PARENT_SCOPE)
endfunction()

# Replaces a dependency on *when a target was linked* with one on *what it is*.
#
# See cmake/HolonicFingerprint.cmake. One stamp per target, shared by every
# founding that reaches it.
function(_holonic_fingerprint target stamp_out)
  set(stamp "${PROJECT_BINARY_DIR}/fingerprints/${target}.hash")
  get_property(fingerprinted GLOBAL PROPERTY HOLONICS_FINGERPRINTED)
  if(NOT target IN_LIST fingerprinted)
    add_custom_command(
      OUTPUT "${stamp}"
      COMMAND "${CMAKE_COMMAND}" "-DBINARY=$<TARGET_FILE:${target}>"
              "-DSTAMP=${stamp}"
              -P "${PROJECT_SOURCE_DIR}/cmake/HolonicFingerprint.cmake"
      DEPENDS ${target}
      COMMENT "fingerprint ${target}"
      VERBATIM)
    set_property(GLOBAL APPEND PROPERTY HOLONICS_FINGERPRINTED ${target})
  endif()
  set(${stamp_out} "${stamp}" PARENT_SCOPE)
endfunction()

# Registers a founding as what it is: a rule that founds files from files.
#
#   NAME         what it is called in build output
#   EXECUTABLE   the deed target, when a deed drives it
#   COMMAND      the argument list, verbatim — inputs and outputs are read off it
#   ALSO_MOUNTS  material reached that no argument names
#   ALSO_RETURNS returns no argument names
#   WITHHOLD     argument keys that are neither mounted nor returned — a scratch
#                region a replay fills and empties is not a founding
function(holonic_found)
  cmake_parse_arguments(FOUND "" "NAME;EXECUTABLE"
    "COMMAND;ALSO_MOUNTS;ALSO_RETURNS;WITHHOLD" ${ARGN})
  if(NOT FOUND_NAME)
    message(FATAL_ERROR "holonic_found requires NAME")
  endif()

  get_property(claimed GLOBAL PROPERTY HOLONICS_CLAIMED_RETURNS)
  set(returns "")
  set(mounts "${FOUND_ALSO_MOUNTS}")
  set(targets "")
  foreach(argument IN LISTS FOUND_COMMAND)
    _holonic_sort("${argument}" "${FOUND_WITHHOLD}" returns mounts targets claimed)
  endforeach()
  foreach(returned IN LISTS FOUND_ALSO_RETURNS)
    if(NOT returned IN_LIST returns)
      list(APPEND returns "${returned}")
      list(APPEND claimed "${returned}")
    endif()
  endforeach()

  if(FOUND_EXECUTABLE)
    set(invocation "$<TARGET_FILE:${FOUND_EXECUTABLE}>" ${FOUND_COMMAND})
    list(APPEND targets "${FOUND_EXECUTABLE}")
  else()
    set(invocation ${FOUND_COMMAND})
  endif()
  list(REMOVE_DUPLICATES targets)
  list(REMOVE_DUPLICATES mounts)

  # An entry that deposits nothing is not a founding — it takes material and
  # returns only a verdict, which is exactly what a test is. It stays in ctest,
  # and the distinction is drawn by what the entry does rather than by what it
  # was called.
  if(NOT returns)
    add_test(NAME ${FOUND_NAME} COMMAND ${invocation})
    return()
  endif()

  set(fingerprints "")
  foreach(target IN LISTS targets)
    _holonic_fingerprint("${target}" stamp)
    list(APPEND fingerprints "${stamp}")
  endforeach()
  list(REMOVE_DUPLICATES returns)
  add_custom_command(
    OUTPUT ${returns}
    COMMAND ${invocation}
    DEPENDS ${fingerprints} ${mounts}
    COMMENT "founding ${FOUND_NAME}"
    JOB_POOL holonic_card
    VERBATIM)

  set_property(GLOBAL PROPERTY HOLONICS_CLAIMED_RETURNS "${claimed}")
  set_property(GLOBAL APPEND PROPERTY HOLONICS_STANDING_RETURNS ${returns})
  set_property(GLOBAL APPEND PROPERTY HOLONICS_MOUNTED_PATHS ${mounts})

  # One line per founding, for the deposit: what produced it, from what, to what.
  # `$<TARGET_FILE:>` resolves at generate time, so the plan carries real paths.
  string(REPLACE ";" "+" plan_mounts "${mounts}")
  string(REPLACE ";" "+" plan_returns "${returns}")
  set(plan_executable "")
  if(FOUND_EXECUTABLE)
    set(plan_executable "$<TARGET_FILE:${FOUND_EXECUTABLE}>")
  endif()
  set_property(GLOBAL APPEND_STRING PROPERTY HOLONICS_STANDING_PLAN
    "${FOUND_NAME}|${plan_executable}|${plan_mounts}|${plan_returns}\n")
endfunction()

# Closes the standing: one target carrying every founded return.
#
# It is deliberately **not** in ALL. Founding is an act, not a side effect of
# compiling, and a deed under diagnosis must not hold the rest of the tree
# hostage. `ninja` builds code; `ninja holonics_standing` brings the standing up
# to date by running exactly the foundings whose closure moved. On an unmoved
# tree that is nothing at all, which is the entire point.
function(holonic_close_standing)
  get_property(returns GLOBAL PROPERTY HOLONICS_STANDING_RETURNS)
  list(LENGTH returns count)
  add_custom_target(holonics_standing DEPENDS ${returns})

  get_property(plan GLOBAL PROPERTY HOLONICS_STANDING_PLAN)
  set(plan_file "${PROJECT_BINARY_DIR}/standing-plan.txt")
  file(GENERATE OUTPUT "${plan_file}" CONTENT "${plan}")

  # Deposits the founded standing into the repository, where it survives a
  # discarded build tree and can be read, diffed and cited.
  #
  # What is deposited is the standing itself — the rested state, the generated
  # proofs, the graded receipts and the seals. What is NOT deposited is the
  # derived bulk: compiled objects and diagnostic atlases, forty megabytes that
  # every deed reproduces byte-identically and that would triple a fifteen
  # megabyte repository to hold. The manifest binds each deposited file to the
  # content hash of the deed binary and of every card and rest it mounted, so a
  # deposit is evidence about a specific founding rather than a copy of a file.
  add_custom_target(holonics_deposit
    COMMAND "${CMAKE_COMMAND}" -DPLAN=${plan_file}
            -DSTANDING=${PROJECT_SOURCE_DIR}/standing
            -DBUILD_ROOT=${PROJECT_BINARY_DIR}
            -P "${PROJECT_SOURCE_DIR}/cmake/HolonicDeposit.cmake"
    COMMENT "depositing the standing"
    VERBATIM)

  message(STATUS "Holonic standing: ${count} founded returns in the build graph")
endfunction()
