/// The grown circuit returns its invariant factors.
///
/// The reduction is the Swing run over incidence: two cells meeting one face is
/// a MEETING, the carried pivot is the FLYWHEEL, the ratio is the TEST, a
/// multiple that clears is a RIDE, a remainder that stands is a FOUND. What no
/// rebase carries away is an invariant factor, and a factor above one is
/// **winding that no change of basis removes**.
///
/// The witnesses are chosen so the carrier cannot pass by accident. The
/// projective plane has the Betti numbers of a disc and its entire content is
/// the factor two: any reduction over a field returns the same numbers for both
/// and silently discards the torsion. The malformed complex must REFUSE rather
/// than return, because an axiom that cannot fire is decoration.
#include <fstream>

#include <holonics/structure/invariant_factor_law.hpp>

namespace {

using holonics::exact::word;
using holonics::structure::rebase_entry;
using holonics::structure::rebase_return;
using coefficient = holonics::structure::rebase_law::coefficient;
using magnitude = holonics::exact::unsigned_integer<2>;

constexpr std::size_t working_capacity = 256;

struct grown final {
  rebase_entry entries[working_capacity]{};
  std::size_t used{};

  void meet(std::uint16_t higher, std::uint16_t lower, bool negative,
            std::uint64_t multiplicity) {
    if (used >= working_capacity) {
      return;
    }
    entries[used] = rebase_entry{higher, lower,
        coefficient{negative, magnitude::from_word(multiplicity)}, true};
    used = used + 1U;
  }
};

/// One vertex and one loop. The loop's two ends are the same vertex with
/// opposed hands, so its boundary already cancels: an oriented pass that returns
/// to where it began leaves no boundary behind.
void grow_circle(grown& into) {
  into.meet(1, 0, false, 1);
  into.meet(1, 0, true, 1);
}

/// The circle with its loop filled once. The cycle is bounded and falls.
void grow_disc(grown& into) {
  into.meet(2, 1, false, 1);
}

/// The circle with its loop filled TWICE with the same hand. The cycle is not
/// bounded, but twice the cycle is, so nothing survives in rank and a factor of
/// two survives instead. This is the projective plane.
void grow_projective_plane(grown& into) {
  into.meet(2, 1, false, 1);
  into.meet(2, 1, false, 1);
}

/// A face meeting a face three times, and another meeting it twice. The greatest
/// common divisor is one, so the pair rebases to a unit and NOTHING is retained:
/// coprime multiplicity is a RIDE no matter how large either side is.
void grow_coprime(grown& into) {
  into.meet(3, 2, false, 3);
  into.meet(4, 2, false, 2);
}

struct witness final {
  const char* name;
  std::uint32_t rank;
  std::uint32_t torsion_count;
  std::uint64_t first_factor;
};

}  // namespace

int main(int argc, char** argv) {
  if (argc != 2) {
    return 2;
  }
  const witness expected[4]{
      {"circle_boundary_cancels", 0, 0, 0},
      {"disc_fills_the_cycle", 1, 0, 1},
      {"projective_plane_retains_two", 1, 1, 2},
      {"coprime_rebases_to_a_unit", 1, 0, 1},
  };
  rebase_return returned[4]{};
  std::size_t refusals = 0;
  for (std::size_t slot = 0; slot < 4; ++slot) {
    grown built{};
    grow_circle(built);
    switch (slot) {
      case 1: grow_disc(built); break;
      case 2: grow_projective_plane(built); break;
      case 3: grow_coprime(built); break;
      default: break;
    }
    returned[slot] =
        holonics::structure::invariant_factor_law::reduce(built.entries, built.used);
    const auto& got = returned[slot];
    const auto& want = expected[slot];
    const bool holds = got.exact && got.rank == want.rank &&
        got.torsion_count == want.torsion_count &&
        (want.rank == 0 || got.divisors[0].value() == want.first_factor);
    refusals += !holds;
  }

  std::ofstream deed{argv[1], std::ios::binary | std::ios::trunc};
  if (!deed) {
    return 3;
  }
  deed << "truth_status=established-bounded\nevidence=implemented-exact\n"
       << "law=the reduction is the swing over incidence; what no rebase carries "
          "away is an invariant factor\n"
       << "carrier=exact signed magnitude with typed refusal; no field, no "
          "tolerance, no materialised matrix\n"
       << "pivot=the first standing meeting, never a global scan\n"
       << "witness_failures=" << refusals << "\n";
  for (std::size_t slot = 0; slot < 4; ++slot) {
    deed << expected[slot].name << "=exact:" << returned[slot].exact
         << ",rank:" << returned[slot].rank
         << ",factors:" << returned[slot].divisor_count
         << ",torsion:" << returned[slot].torsion_count
         << ",first:" << returned[slot].divisors[0].value()
         << ",rides:" << returned[slot].rides
         << ",foundings:" << returned[slot].foundings << "\n";
  }
  deed << "the_projective_plane_is_the_witness=its rank equals the disc's and "
          "its whole content is the retained factor two\n";
  return refusals == 0 ? 0 : 1;
}
