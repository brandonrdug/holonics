#include <cstdint>
#include <fstream>
#include <iostream>

#include <holonics/body/standing_residency.hpp>
#include <holonics/organ/constraint_cycle_reading.hpp>

#include "one_standing_report.hpp"

namespace {

using holonics::body::returned_standing;
using holonics::exact::word;
using holonics::organ::constraint_degree;
using holonics::organ::cycle_type;
namespace law = holonics::organ::constraint_law;

/// Declared identities for the three organs this current may found. They are
/// names in the standing, not slots: exclusion cascades along them.
constexpr word transitivity_organ{0x5452'414E'0000'0001ULL};
constexpr word transposition_organ{0x5452'5053'0000'0002ULL};
constexpr word verdict_organ{0x5645'5244'0000'0003ULL};

constexpr std::int64_t constraint[constraint_degree + 1] = {-1, -1, 0, 0, 0, 1};
constexpr std::uint16_t aperture[6] = {2, 3, 5, 7, 11, 13};

/// A cycle type, as exact words a later current can read back.
[[nodiscard]] std::uint32_t organ_words(
    const cycle_type& type,
    std::uint64_t* out) noexcept {
  out[0] = type.prime;
  for (std::uint8_t slot = 0; slot < type.used; ++slot) {
    out[1U + slot] = type.degrees[slot];
  }
  return 1U + type.used;
}

/// The later mathematical current. It does not recompute anything: it **reaches**
/// what earlier returns deposited, and what it can conclude is exactly what
/// stands. With no verdict reachable it does not guess — it stands OPEN.
struct later_conduct final {
  bool verdict_reached{};
  bool refuses_radical_chart{};
  bool rebases_to_finite_chart{};
  std::uint64_t rebase_prime{};
  bool stands_open{};
};

template<class Standing>
[[nodiscard]] later_conduct conduct(const Standing& body) noexcept {
  later_conduct out{};
  const auto* verdict = body.reach(verdict_organ);
  if (verdict == nullptr) {
    out.stands_open = true;
    return out;
  }
  out.verdict_reached = true;
  out.refuses_radical_chart = body.word_at(*verdict, 0) ==
      static_cast<std::uint64_t>(holonics::organ::chart_obstruction::group_not_solvable);
  const auto* transposition = body.reach(transposition_organ);
  if (transposition != nullptr) {
    out.rebases_to_finite_chart = true;
    out.rebase_prime = body.word_at(*transposition, 0);
  }
  return out;
}

}  // namespace

int main(int argument_count, char** arguments) {
  if (argument_count != 2) {
    std::cerr << "expected one artifact path\n";
    return 2;
  }
  returned_standing<8, 64> body{};

  // The earlier mathematical current. Each reading that proves something is
  // deposited as a returned organ; readings that prove nothing deposit nothing.
  cycle_type transitive{};
  cycle_type transposed{};
  for (const auto prime : aperture) {
    std::uint16_t factors[constraint_degree * (constraint_degree + 1)]{};
    const auto type = law::read_cycle_type(constraint, prime, factors);
    if (!type.admitted()) {
      continue;
    }
    if (law::witnesses_transitivity(type) && transitive.used == 0) {
      transitive = type;
    }
    if (law::carries_transposition(type) && transposed.used == 0) {
      transposed = type;
    }
  }
  if (transitive.used == 0 || transposed.used == 0) {
    std::cerr << "the aperture returned no witness pair\n";
    return 3;
  }

  std::uint64_t words[constraint_degree + 2]{};
  const bool founded =
      body.deposit(transitivity_organ, words, organ_words(transitive, words), word{}) !=
          holonics::body::no_deposit &&
      body.deposit(transposition_organ, words, organ_words(transposed, words), word{}) !=
          holonics::body::no_deposit;
  if (!founded) {
    std::cerr << "witness deposit refused\n";
    return 4;
  }

  // The verdict is composed from what stands, and is depositable only because
  // both witnesses stand. It names the transitivity organ as its cause.
  const bool both = body.reach(transitivity_organ) != nullptr &&
      body.reach(transposition_organ) != nullptr;
  std::uint64_t verdict[1]{static_cast<std::uint64_t>(
      both ? holonics::organ::chart_obstruction::group_not_solvable
           : holonics::organ::chart_obstruction::witnesses_insufficient)};
  const bool verdict_founded =
      body.deposit(verdict_organ, verdict, 1, transitivity_organ) !=
      holonics::body::no_deposit;

  const auto standing_conduct = conduct(body);
  const std::uint32_t standing_before = body.standing();

  // THE REST CARRIES THE STANDING. Variable extent, proportional to the derived
  // population, and a fresh body founded from those octets alone.
  unsigned char image[2048]{};
  const auto rest_octets = holonics::body::standing_rest_law::encode(body, image, 2048);
  returned_standing<8, 64> remounted{};
  const bool remount_founded =
      holonics::body::standing_rest_law::decode(remounted, image, rest_octets);
  const bool remount_exact = remount_founded &&
      holonics::body::standing_rest_law::same_standing(body, remounted);
  const auto remount_conduct = conduct(remounted);

  // RIDE ACTUALLY RIDES. Mount once; synchronize again against an unchanged
  // standing and the chart does no work at all; then append one organ and only
  // the appended octets cross.
  holonics::body::standing_residency<2048> chart{};
  const bool mounted = chart.synchronize(body);
  const bool rode = chart.synchronize(body);
  std::uint64_t appended[1]{holonics::organ::constraint_degree};
  static_cast<void>(body.deposit(word{0x4150'5044'0000'0004ULL}, appended, 1, word{}));
  const bool grew = chart.synchronize(body);
  const auto residency = chart.receipt();
  static_cast<void>(body.exclude(word{0x4150'5044'0000'0004ULL}));

  // THE MANDATORY RECEIPT. Three continuation fibers, a typed return mode, and a
  // complete obstruction rather than a scalar confidence.
  holonics::current::causal_information_receipt<8, 4, 4> receipt{};
  namespace fiber = holonics::current::fiber_law;
  for (const auto prime : aperture) {
    static_cast<void>(fiber::try_admit(receipt.before_contact, word{prime}, false));
  }
  static_cast<void>(fiber::try_admit(receipt.after_world_return,
      word{transitive.prime}, true));
  static_cast<void>(fiber::try_admit(receipt.after_world_return,
      word{transposed.prime}, true));
  static_cast<void>(fiber::try_admit(receipt.after_emanated_return, verdict_organ, true));
  receipt.world_return = fiber::classify(receipt.before_contact, receipt.after_world_return);
  receipt.answer_return =
      fiber::classify(receipt.after_world_return, receipt.after_emanated_return);
  receipt.morphology = holonics::current::morphology_change::founded;
  receipt.work.committed_passages = body.deposits();
  receipt.work.causal_span = 2;
  receipt.work.exposed_parallel_width = standing_before;
  receipt.obstruction =
      word{static_cast<std::uint64_t>(holonics::organ::chart_obstruction::group_not_solvable)};
  receipt.artifact_returned = true;

  // The exclusion. One earlier return leaves the standing; everything that stood
  // only because of it falls with it. No flag is set and no counter moves.
  const std::uint32_t fallen = body.exclude(transitivity_organ);
  const auto ablated_conduct = conduct(body);

  std::ofstream artifact(arguments[1]);
  if (!artifact) {
    return 5;
  }
  write_one_standing(artifact, transitive, transposed, verdict_founded, standing_before,
      body.deposits(), standing_conduct, rest_octets, remount_founded, remount_exact,
      remount_conduct, mounted, rode, grew, residency, receipt, fallen, body.standing(),
      body.exclusions(), ablated_conduct);

  const bool holds = remount_exact && remount_conduct.verdict_reached && mounted && rode &&
      grew && residency.rides == 1 && residency.full_mounts == 1 &&
      residency.appended_organs == 1 && residency.avoided_octets > 0 &&
      receipt.artifact_returned && receipt.before_contact.used == 6 &&
      receipt.after_emanated_return.used == 1 &&
      verdict_founded && standing_conduct.verdict_reached &&
      standing_conduct.refuses_radical_chart && standing_conduct.rebases_to_finite_chart &&
      !standing_conduct.stands_open && fallen == 2 && body.standing() == 1 &&
      !ablated_conduct.verdict_reached && !ablated_conduct.refuses_radical_chart &&
      ablated_conduct.stands_open;

  std::cerr << "rest " << rest_octets << " octets, remount "
            << (remount_exact ? "exact" : "INEXACT") << "; residency "
            << residency.full_mounts << " mount / " << residency.rides << " ride / "
            << residency.appended_organs << " append, " << residency.avoided_octets
            << " octets avoided\n";
  std::cerr << "one standing: " << standing_before << " organs deposited; later current "
            << (standing_conduct.refuses_radical_chart ? "refuses the radical chart"
                                                       : "DID NOT REFUSE")
            << "; after excluding one return " << fallen << " fell and the later current "
            << (ablated_conduct.stands_open ? "stands OPEN" : "STILL CONCLUDED") << '\n';
  if (!holds) {
    std::cerr << "ONE STANDING FAILED: the deposit did not condition later conduct\n";
    return 6;
  }
  return 0;
}
