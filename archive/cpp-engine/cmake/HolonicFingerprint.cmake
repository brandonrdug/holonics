# A founding depends on what its deed IS, not on when it was linked.
#
# ninja marks a founding dirty when the deed target is rebuilt, and a rebuild is
# not a change: editing a comment in a header the deed includes recompiles the
# translation unit, relinks, strips, and produces a **byte-identical** binary.
# Under a timestamp dependency that costs the whole downstream chain — for the
# trace-rebase line, twenty-odd minutes of exact integer work to reproduce what
# already stood.
#
# This writes the deed's content hash and **rewrites it only when the hash
# moved**. The founding edges carry `restat = 1`, so an unchanged stamp keeps its
# timestamp, ninja re-stats it, and nothing downstream is disturbed.

foreach(required IN ITEMS BINARY STAMP)
  if(NOT DEFINED ${required})
    message(FATAL_ERROR "holonic fingerprint requires ${required}")
  endif()
endforeach()

file(SHA256 "${BINARY}" current)
set(previous "")
if(EXISTS "${STAMP}")
  file(READ "${STAMP}" previous)
endif()
if(NOT previous STREQUAL current)
  file(WRITE "${STAMP}" "${current}")
endif()
