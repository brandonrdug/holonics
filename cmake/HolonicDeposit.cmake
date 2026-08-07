# Deposits the founded standing into the repository.
#
# The machine's entire founded mathematical production lived in a gitignored
# build directory: 111,000 octets of rested state across 23 files, and the
# generated proofs beside them. A discarded build tree destroyed all of it, and
# recovering it meant re-deriving from zero. That is precisely what a weight file
# exists to prevent.
#
# What is deposited is the standing: the rested state, the generated formal
# sources, the graded deed receipts, the seals and the post-seal comparisons.
#
# What is NOT deposited is the derived bulk — compiled objects and diagnostic
# atlases, some forty megabytes that every deed reproduces byte-identically from
# the same inputs. Holding that in a fifteen megabyte repository would triple it
# to store material the machine regenerates exactly. The consequence is stated
# rather than hidden: **a fresh build tree still founds once.** The compiled
# object and the atlases come out of the same single deed execution as the rest,
# so they cannot be split from it, and adopting a partial standing would let
# ninja believe a founding was complete when it was not.
#
# The manifest is what makes this evidence rather than a copy. Each entry carries
# the deposited file's content hash AND the closure hash of its founding — the
# hash of the deed binary together with every card and rest it mounted. A
# deposited return can therefore be checked against the exact deed and exact
# material that produced it, which is the same certificate the determinism
# replays and source-access audits establish at run time.

foreach(required IN ITEMS PLAN STANDING BUILD_ROOT)
  if(NOT DEFINED ${required})
    message(FATAL_ERROR "holonic deposit requires ${required}")
  endif()
endforeach()

# The standing carries meaning; the rest is reproducible receipt.
set(deposited_suffixes ".rest" ".lean")
set(deposited_patterns "/receipts/" "POST_SEAL" "DOSSIER")
set(refused_patterns "STDOUT" "STDERR" "OPEN_PATHS")

file(STRINGS "${PLAN}" plan_lines)
set(manifest "")
set(deposited_count 0)
set(deposited_octets 0)
set(refused_count 0)

foreach(line IN LISTS plan_lines)
  if(line STREQUAL "")
    continue()
  endif()
  string(REPLACE "|" ";" fields "${line}")
  list(GET fields 0 founding)
  list(GET fields 1 executable)
  list(GET fields 2 packed_mounts)
  list(GET fields 3 packed_returns)
  string(REPLACE "+" ";" mounts "${packed_mounts}")
  string(REPLACE "+" ";" returns "${packed_returns}")

  # The closure hash: what founded this, and out of what.
  set(closure_material "")
  if(executable AND EXISTS "${executable}")
    file(SHA256 "${executable}" executable_hash)
    string(APPEND closure_material "${executable_hash}")
  endif()
  foreach(mount IN LISTS mounts)
    if(EXISTS "${mount}" AND NOT IS_DIRECTORY "${mount}")
      file(SHA256 "${mount}" mount_hash)
      string(APPEND closure_material "${mount_hash}")
    endif()
  endforeach()
  string(SHA256 closure "${closure_material}")

  foreach(returned IN LISTS returns)
    if(NOT EXISTS "${returned}")
      continue()
    endif()

    set(refused FALSE)
    foreach(pattern IN LISTS refused_patterns)
      if(returned MATCHES "${pattern}")
        set(refused TRUE)
        break()
      endif()
    endforeach()

    set(carries_standing FALSE)
    if(NOT refused)
      foreach(suffix IN LISTS deposited_suffixes)
        if(returned MATCHES "\\${suffix}$")
          set(carries_standing TRUE)
          break()
        endif()
      endforeach()
      foreach(pattern IN LISTS deposited_patterns)
        if(returned MATCHES "${pattern}")
          set(carries_standing TRUE)
          break()
        endif()
      endforeach()
    endif()

    if(NOT carries_standing)
      math(EXPR refused_count "${refused_count}+1")
      continue()
    endif()

    file(RELATIVE_PATH relative "${BUILD_ROOT}" "${returned}")
    file(SHA256 "${returned}" content)
    file(SIZE "${returned}" octets)
    configure_file("${returned}" "${STANDING}/${relative}" COPYONLY)
    string(APPEND manifest "${relative} ${content} ${closure} ${founding}\n")
    math(EXPR deposited_count "${deposited_count}+1")
    math(EXPR deposited_octets "${deposited_octets}+${octets}")
  endforeach()
endforeach()

file(WRITE "${STANDING}/MANIFEST.txt"
  "truth_status=established-bounded\n"
  "evidence=computational-witness\n"
  "law=a deposited return names the deed binary and the material it mounted\n"
  "columns=path content_sha256 closure_sha256 founding\n"
  "deposited_returns=${deposited_count}\n"
  "deposited_octets=${deposited_octets}\n"
  "derived_returns_not_deposited=${refused_count}\n"
  "${manifest}")

message(STATUS
  "deposited ${deposited_count} founded returns, ${deposited_octets} octets; "
  "${refused_count} derived returns left to be reproduced")
