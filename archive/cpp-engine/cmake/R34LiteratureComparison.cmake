cmake_minimum_required(VERSION 4.3.2 FATAL_ERROR)
foreach(required IN ITEMS SEAL SOURCE LAW_ATLAS LITERATURE OUTPUT)
  if(NOT DEFINED ${required})
    message(FATAL_ERROR "R34 literature comparison requires ${required}")
  endif()
endforeach()
foreach(required IN ITEMS SEAL SOURCE LAW_ATLAS LITERATURE)
  if(NOT EXISTS "${${required}}")
    message(FATAL_ERROR "R34 literature comparison requires ${required}")
  endif()
endforeach()
file(SHA256 "${SEAL}" seal_before)
file(READ "${SOURCE}" formal)
file(READ "${LAW_ATLAS}" laws)
file(READ "${LITERATURE}" literature)
foreach(needle IN ITEMS "Goldman" "x123 + x132" "x123*x132"
    "double branched cover" "arXiv:0901.1404")
  string(FIND "${literature}" "${needle}" position)
  if(position EQUAL -1)
    message(FATAL_ERROR "R34 literature source omits ${needle}")
  endif()
endforeach()
foreach(needle IN ITEMS "def traceSumPolynomial" "def traceProductPolynomial"
    "theorem discoveredTraceFiber" "candidate\t3\t0\t0\t5184\t85\t84\t1\t0\t1"
    "candidate\t7\t1\t0\t5184\t85\t84\t1\t0\t1")
  string(FIND "${formal}${laws}" "${needle}" position)
  if(position EQUAL -1)
    message(FATAL_ERROR "R34 sealed return omits ${needle}")
  endif()
endforeach()
file(SHA256 "${SEAL}" seal_after)
if(NOT seal_before STREQUAL seal_after)
  message(FATAL_ERROR "R34 seal changed during literature comparison")
endif()
file(WRITE "${OUTPUT}" "# R34 post-seal literature comparison\n\n"
  "**Truth status:** `interpretation`.\n\n"
  "Under `x1=a`, `x2=b`, `x3=c`, `x12=d`, `x13=e`, and `x23=f`, the sealed "
  "sum organ states `p+q=cd+be+af-abc`. Its product organ states "
  "`pq=a^2+b^2+c^2+d^2+e^2+f^2-abd-ace-bcf+def-4`. These agree exactly "
  "with Goldman's rank-three triple-trace sum and product relations.\n\n"
  "The literature consequently identifies the composed monic quadratic as the classical "
  "rank-three character-ring hypersurface and its projection as a double branched cover of "
  "the six lower trace coordinates. The seal remained byte-identical (`${seal_before}`). "
  "The general identities receive `proved-standard`; the 5,184-row census, 2,072 bounded "
  "archetypes, branch distribution, collision atlas, and heldout transport retain "
  "`established-bounded`. No full matrix reconstruction, arbitrary character-variety, Hodge, "
  "or RH consequence follows.\n")
