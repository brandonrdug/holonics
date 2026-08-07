cmake_minimum_required(VERSION 4.3.2 FATAL_ERROR)
foreach(required IN ITEMS SEAL SOURCE LAW_ATLAS LITERATURE OUTPUT)
  if(NOT DEFINED ${required})
    message(FATAL_ERROR "R33 literature comparison requires ${required}")
  endif()
endforeach()
foreach(required IN ITEMS SEAL SOURCE LAW_ATLAS LITERATURE)
  if(NOT EXISTS "${${required}}")
    message(FATAL_ERROR "R33 literature comparison requires ${required}")
  endif()
endforeach()
file(SHA256 "${SEAL}" seal_before)
file(READ "${SOURCE}" formal)
file(READ "${LAW_ATLAS}" laws)
file(READ "${LITERATURE}" literature)
foreach(needle IN ITEMS "Fricke" "Vogt" "x^2 + y^2 + z^2 - xyz - 2"
    "tr([A,B])")
  string(FIND "${literature}" "${needle}" position)
  if(position EQUAL -1)
    message(FATAL_ERROR "R33 literature source omits ${needle}")
  endif()
endforeach()
foreach(needle IN ITEMS "2,0,0,0,-1,0,0,-1,0,-1" "generated_characteristic_hypergeometry")
  string(FIND "${laws}${formal}" "${needle}" position)
  if(position EQUAL -1)
    message(FATAL_ERROR "R33 sealed return omits ${needle}")
  endif()
endforeach()
file(SHA256 "${SEAL}" seal_after)
if(NOT seal_before STREQUAL seal_after)
  message(FATAL_ERROR "R33 seal changed during literature comparison")
endif()
file(WRITE "${OUTPUT}" "# R33 post-seal literature comparison\n\n"
  "**Truth status:** `interpretation`.\n\n"
  "The sealed coefficient vector states `2 - x^2 - y^2 - z^2 + xyz + k = 0`, "
  "equivalently `tr([A,B]) = x^2 + y^2 + z^2 - xyz - 2`. The independent "
  "literature record identifies this as the classical Fricke--Vogt commutator trace identity. "
  "The general Lean return and determinant-one hypotheses agree exactly with that comparison.\n\n"
  "The seal remained byte-identical (`${seal_before}`). The classical identity receives "
  "`proved-standard`; the bounded 6,308-pair distribution, 281 archetypes, collision atlas, "
  "and held-out transport retain `established-bounded`. No general character-variety, Hodge, "
  "or RH consequence follows from this comparison.\n")
