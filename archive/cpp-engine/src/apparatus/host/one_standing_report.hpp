#pragma once

#include <ostream>

#include <holonics/body/standing_residency.hpp>
#include <holonics/current/information_receipt.hpp>

/// The exterior report for the one-standing deed. Split from the deed so the
/// deed stays inside the file-size law; it carries no law of its own.
template<class Transitive, class Transposed, class Conduct, class Receipt>
void write_one_standing(
    std::ostream& artifact,
    const Transitive& transitive,
    const Transposed& transposed,
    bool verdict_founded,
    std::uint32_t standing_before,
    std::uint64_t deposits,
    const Conduct& standing_conduct,
    std::uint32_t rest_octets,
    bool remount_founded,
    bool remount_exact,
    const Conduct& remount_conduct,
    bool mounted,
    bool rode,
    bool grew,
    const holonics::body::residency_receipt& residency,
    const Receipt& receipt,
    std::uint32_t fallen,
    std::uint32_t standing_after,
    std::uint64_t exclusions,
    const Conduct& ablated_conduct) {
  artifact << "# The one-standing deed\n\n";
  artifact << "A mathematical return deposits structure into the standing that\n";
  artifact << "conditions later mathematical conduct. Before this, a mathematical\n";
  artifact << "deed committed a tally and its return could condition nothing.\n\n";
  artifact << "## the earlier current\n\n";
  artifact << "transitivity witnessed at p=" << transitive.prime << ", deposited\n";
  artifact << "transposition witnessed at p=" << transposed.prime << ", deposited\n";
  artifact << "verdict composed from both and deposited "
           << (verdict_founded ? "yes" : "no") << '\n';
  artifact << "organs standing " << standing_before << '\n';
  artifact << "deposits " << deposits << "\n\n";
  artifact << "## the later current, reaching only what stands\n\n";
  artifact << "verdict reached " << (standing_conduct.verdict_reached ? "yes" : "no") << '\n';
  artifact << "refuses the radical chart "
           << (standing_conduct.refuses_radical_chart ? "yes" : "no") << '\n';
  artifact << "rebases to the finite chart at p=" << standing_conduct.rebase_prime << '\n';
  artifact << "stands open " << (standing_conduct.stands_open ? "yes" : "no") << "\n\n";
  artifact << "## the rest carries the standing\n\n";
  artifact << "rest octets " << rest_octets << " (variable, proportional to the population)\n";
  artifact << "founded from those octets alone " << (remount_founded ? "yes" : "no") << '\n';
  artifact << "remount exact " << (remount_exact ? "yes" : "no") << '\n';
  artifact << "the remounted body reaches the verdict "
           << (remount_conduct.verdict_reached ? "yes" : "no") << " without re-deriving\n\n";
  artifact << "## RIDE actually rides\n\n";
  artifact << "first synchronize mounted " << (mounted ? "yes" : "no") << '\n';
  artifact << "second synchronize against unchanged standing rode "
           << (rode ? "yes" : "no") << '\n';
  artifact << "third synchronize after one deposit grew " << (grew ? "yes" : "no") << '\n';
  artifact << "full mounts " << residency.full_mounts << '\n';
  artifact << "rides " << residency.rides << '\n';
  artifact << "append deltas " << residency.appended_organs << '\n';
  artifact << "octets mounted " << residency.mounted_octets << '\n';
  artifact << "octets avoided " << residency.avoided_octets << "\n\n";
  artifact << "## the causal-information receipt\n\n";
  artifact << "continuation fibers 3 (before contact, after world return, after emanated)\n";
  artifact << "before contact " << receipt.before_contact.used << " currents, "
           << receipt.before_contact.open << " open\n";
  artifact << "after world return " << receipt.after_world_return.used << " currents, "
           << receipt.after_world_return.closed << " closed\n";
  artifact << "after emanated return " << receipt.after_emanated_return.used << '\n';
  artifact << "world return mode " << static_cast<unsigned>(receipt.world_return) << '\n';
  artifact << "morphology change " << static_cast<unsigned>(receipt.morphology) << '\n';
  artifact << "obstruction carried complete " << receipt.obstruction.value() << '\n';
  artifact << "artifact returned " << (receipt.artifact_returned ? "yes" : "no") << "\n\n";
  artifact << "## the structural exclusion\n\n";
  artifact << "transitivity organ excluded; organs fallen " << fallen << '\n';
  artifact << "organs standing " << standing_after << '\n';
  artifact << "exclusions " << exclusions << '\n';
  artifact << "verdict reachable " << (ablated_conduct.verdict_reached ? "yes" : "no") << '\n';
  artifact << "refuses the radical chart "
           << (ablated_conduct.refuses_radical_chart ? "yes" : "no") << '\n';
  artifact << "stands open " << (ablated_conduct.stands_open ? "yes" : "no") << '\n';

}
