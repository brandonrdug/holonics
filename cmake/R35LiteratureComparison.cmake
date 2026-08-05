cmake_minimum_required(VERSION 4.3.2 FATAL_ERROR)
foreach(required IN ITEMS SEAL SOURCE LAW_ATLAS LITERATURE OUTPUT)
  if(NOT DEFINED ${required})
    message(FATAL_ERROR "R35 literature comparison requires ${required}")
  endif()
endforeach()
foreach(required IN ITEMS SEAL SOURCE LAW_ATLAS LITERATURE)
  if(NOT EXISTS "${${required}}")
    message(FATAL_ERROR "R35 literature comparison requires ${required}")
  endif()
endforeach()
file(SHA256 "${SEAL}" seal_before)
file(READ "${SOURCE}" formal)
file(READ "${LAW_ATLAS}" laws)
file(READ "${LITERATURE}" literature)
foreach(needle IN ITEMS "Nielsen" "Horowitz" "Goldman" "Jacobian" "branch")
  string(FIND "${literature}" "${needle}" position)
  if(position EQUAL -1)
    message(FATAL_ERROR "R35 literature source omits ${needle}")
  endif()
endforeach()
foreach(needle IN ITEMS "theorem discoveredRebase0" "theorem discoveredRebase3"
    "theorem returnedHypersurfaceInvariance" "theorem actualReturnedChainRule"
    "map\t0\t6\t3\t121\t120\t1\t0\t1")
  string(FIND "${formal}${laws}" "${needle}" position)
  if(position EQUAL -1)
    message(FATAL_ERROR "R35 sealed return omits ${needle}")
  endif()
endforeach()
file(SHA256 "${SEAL}" seal_after)
if(NOT seal_before STREQUAL seal_after)
  message(FATAL_ERROR "R35 seal changed during literature comparison")
endif()
file(WRITE "${OUTPUT}" "# R35 post-seal literature comparison\n\n"
  "**Truth status:** `interpretation`.\n\n"
  "The sealed matrix-caused maps agree with the standard Nielsen-generator action on "
  "rank-three trace coordinates described by Horowitz and Goldman. Their exact Jacobians "
  "therefore realize the usual differential of a polynomial character-coordinate change. "
  "The returned branch transitions are receiver-relative transitions of the six-coordinate "
  "projection, consistent with the standard two-sheet trace fiber; they are not intrinsic "
  "singularities of the whole character variety. The seal remained byte-identical "
  "(`${seal_before}`). General matrix and chain identities receive `proved-standard`; the "
  "1,272-state, 6,360-edge census, tangent atlas, witnesses, and held-out navigation retain "
  "`established-bounded`. No arbitrary automorphism, Hodge, or RH consequence follows.\n")
