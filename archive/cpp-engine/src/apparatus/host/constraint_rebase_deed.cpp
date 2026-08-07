#include <cstdint>
#include <fstream>
#include <iostream>

#include <holonics/organ/constraint_cycle_reading.hpp>

namespace {

using holonics::organ::chart_obstruction;
using holonics::organ::constraint_degree;
using holonics::organ::cycle_type;
using holonics::organ::obstruction_witness;
namespace law = holonics::organ::constraint_law;

/// The declared prime aperture. It is walked in order and abandoned as soon as
/// the witnesses decide, which is the whole point: the body beelines to the
/// case that settles the question instead of sweeping the family.
constexpr std::uint16_t primes[36] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41,
    43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131,
    137, 139, 149, 151};

/// Two constraints of the same shape and different reach. Coefficients are low
/// first: the unknown is the root, and the question is which chart determines it.
constexpr std::int64_t unreachable[constraint_degree + 1] = {-1, -1, 0, 0, 0, 1};
constexpr std::int64_t reachable[constraint_degree + 1] = {-2, 0, 0, 0, 0, 1};

void write_type(std::ostream& out, const cycle_type& type) {
  out << "p=" << type.prime << " type=(";
  for (std::uint8_t slot = 0; slot < type.used; ++slot) {
    out << (slot == 0 ? "" : ",") << static_cast<unsigned>(type.degrees[slot]);
  }
  out << ") squarefree=" << (type.squarefree ? "yes" : "no")
      << " product=" << (type.product_agrees ? "agrees" : "disagrees");
}

/// Walk the declared prime aperture, reading the constraint's local chart at
/// each and keeping only what proves something. **The witnesses are the deed**:
/// one prime that proves transitivity, one that proves a transposition stands.
[[nodiscard]] obstruction_witness gather(
    const std::int64_t* coefficients,
    std::ostream& out) {
  obstruction_witness witness{};
  for (const auto prime : primes) {
    std::uint16_t factors[constraint_degree * (constraint_degree + 1)]{};
    const auto type = law::read_cycle_type(coefficients, prime, factors);
    out << "  ";
    write_type(out, type);
    if (!type.admitted()) {
      out << " -> reduction degenerate, not read\n";
      continue;
    }
    const bool transitive = law::witnesses_transitivity(type);
    const bool transposition = law::carries_transposition(type);
    out << (transitive ? " -> transitivity" : "")
        << (transposition ? " -> transposition" : "")
        << (!transitive && !transposition ? " -> no new witness" : "") << '\n';
    if (transitive && !witness.transitive) {
      witness.transitive = true;
      witness.transitive_prime = prime;
      witness.transitive_type = type;
    }
    if (transposition && !witness.carries_transposition) {
      witness.carries_transposition = true;
      witness.transposition_prime = prime;
      witness.transposition_type = type;
    }
    if (witness.transitive && witness.carries_transposition) {
      out << "  both witnesses stand; the aperture is not walked further\n";
      break;
    }
  }
  return witness;
}

}  // namespace

int main(int argument_count, char** arguments) {
  if (argument_count != 2) {
    std::cerr << "expected one artifact path\n";
    return 2;
  }
  std::ofstream artifact(arguments[1]);
  if (!artifact) {
    return 3;
  }

  artifact << "# The constraint rebase deed\n\n";
  artifact << "A constraint is a Chi: two transports asserted equal. The unknown is\n";
  artifact << "whatever the present chart does not determine.\n\n";

  artifact << "## the constraint x^5 - x - 1, read across the prime aperture\n\n";
  const auto witness = gather(unreachable, artifact);
  const auto verdict = witness.verdict();
  artifact << "\ntransitivity witnessed at p=" << witness.transitive_prime << '\n';
  artifact << "transposition witnessed at p=" << witness.transposition_prime << '\n';
  artifact << "obstruction " << static_cast<unsigned>(verdict);
  artifact << (verdict == chart_obstruction::group_not_solvable
                   ? " (the group is the whole symmetric group on five points,\n"
                     "  which is not solvable, so no tower of cyclic charts reaches\n"
                     "  the root: the unknown is unreachable by radicals)\n\n"
                   : " (the witnesses do not yet decide)\n\n");

  artifact << "## the rebase\n\n";
  std::uint16_t factors[constraint_degree * (constraint_degree + 1)]{};
  const auto local = law::read_cycle_type(unreachable, witness.transposition_prime, factors);
  artifact << "the chart the obstruction names is the finite one at p="
           << witness.transposition_prime << ", where the unknown IS determined:\n";
  std::uint8_t at = 0;
  for (std::uint8_t held = 0; held < local.used; ++held) {
    artifact << "  factor of degree " << static_cast<unsigned>(local.degrees[held]) << ":";
    for (std::uint8_t slot = 0; slot <= local.degrees[held]; ++slot) {
      artifact << ' ' << factors[(held * (constraint_degree + 1)) + slot];
    }
    artifact << '\n';
    at = static_cast<std::uint8_t>(at + local.degrees[held]);
  }
  artifact << "  the factor degrees account for " << static_cast<unsigned>(at)
           << " of " << static_cast<unsigned>(constraint_degree) << " roots\n";
  artifact << "  the product of the factors equals the reduction: "
           << (local.product_agrees ? "yes" : "no") << "\n\n";

  artifact << "## the invariant across charts\n\n";
  artifact << "the two readings differ as charts and agree as a group:\n  ";
  write_type(artifact, witness.transitive_type);
  artifact << "\n  ";
  write_type(artifact, witness.transposition_type);
  artifact << "\nboth cycle types are realized inside one group, and it is that group,\n";
  artifact << "not either local reading, that the body retains\n\n";

  artifact << "## the control x^5 - 2, whose unknown the radical chart does reach\n\n";
  std::uint16_t roots[constraint_degree]{};
  std::uint8_t root_count = 0;
  std::uint16_t split_prime = 0;
  std::uint16_t primes_walked = 0;
  for (const auto prime : primes) {
    primes_walked = static_cast<std::uint16_t>(primes_walked + 1U);
    if (law::roots_form_radical_coset(reachable, prime, roots, root_count)) {
      split_prime = prime;
      break;
    }
  }
  if (split_prime == 0) {
    artifact << "no prime inside the declared aperture split it; the aperture is the\n";
    artifact << "boundary of this reading and is recorded rather than widened\n";
  } else {
    artifact << "at p=" << split_prime << " the roots are";
    for (std::uint8_t slot = 0; slot < root_count; ++slot) {
      artifact << ' ' << roots[slot];
    }
    artifact << "\nand they form a coset of the fifth roots of unity: every root is one\n";
    artifact << "root times a unit, which is the radical tower witnessed locally\n";
    artifact << "the aperture was walked " << primes_walked
             << " primes deep before the case appeared\n";
  }
  artifact << "\nthe same shape of constraint; different reach; the difference is proved\n";
  artifact << "and not assumed\n";

  std::cerr << "constraint rebase: x^5-x-1 transitive at p=" << witness.transitive_prime
            << ", transposition at p=" << witness.transposition_prime
            << ", obstruction=" << static_cast<unsigned>(verdict)
            << "; x^5-2 splits as a radical coset at p=" << split_prime << '\n';
  if (verdict != chart_obstruction::group_not_solvable || !local.admitted() ||
      split_prime == 0) {
    std::cerr << "CONSTRAINT REBASE FAILED\n";
    return 4;
  }
  return 0;
}
