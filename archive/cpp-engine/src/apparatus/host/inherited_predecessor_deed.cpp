/// Founds the inherited predecessor rest.
///
/// The record this writes was a **committed 320-octet binary** under
/// `apparatus/rests/` until 2026-08-07. It is the handoff the geometry-inquiry
/// deed emitted before that deed was cut on 2026-08-06 — cut because every
/// verdict-bearing field in its law was a compile-time constant for every
/// admissible input, so the rest it produced was already the computation's only
/// possible output.
///
/// Retaining it as a blob was correct about the mathematics and wrong about the
/// apparatus. A rest image is a **layout**, and the excision of the admitted
/// tally changed that layout: the blob went stale silently and every deed
/// downstream of it failed on a mount that could not be read. A constant that
/// only source can describe belongs in source.
///
/// So the constant is constructed here, from the same declaration the host
/// oracle uses, and rested through the same writer every other deed rests
/// through. It is now a founding like any other: its closure is this executable,
/// and a layout change re-founds it instead of breaking it.
#include <fstream>

#include "r18_cases.hpp"

int main(int argc, char **argv) {
  if (argc != 2)
    return 2;
  const auto record = holonics::tests::r18_host_geometry_rest();
  std::ofstream rest{argv[1], std::ios::binary | std::ios::trunc};
  if (!rest)
    return 3;
  rest.write(reinterpret_cast<const char *>(&record), sizeof(record));
  return rest.good() ? 0 : 4;
}
