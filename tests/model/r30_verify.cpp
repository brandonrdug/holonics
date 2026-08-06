#include "r30_verify.hpp"

#include "r30_reference.hpp"
#include "r30_reference_field.hpp"

namespace holonics::tests {
namespace {
template <std::size_t N, class Count, std::size_t M>
bool contains(const char (&b)[N], Count used, const char (&p)[M]) {
  for (std::size_t i = 0; i + M - 1 <= used; ++i) {
    bool same = true;
    for (std::size_t j = 0; j < M - 1; ++j)
      same = same && b[i + j] == p[j];
    if (same)
      return true;
  }
  return false;
}
} // namespace
std::size_t r30_verification_failures(
    bool loaded, const apparatus::rederivation_store_receipt &rest_load,
    const apparatus::rederivation_executor_receipt &execution,
    const event::rederivation_observation &o,
    const organ::rederivation_workspace &w,
    const event::rederivation_rest_record &h) noexcept {
  const auto ref = r30_reference();
  std::size_t f = !loaded || !rest_load.returned() || !execution.returned() ||
                  !ref.exact || execution.kernel_launches != exact::word{12} ||
                  execution.semantic_threads != exact::word{2'415} ||
                  execution.host_semantic_events != exact::word{0} ||
                  execution.source_currents != exact::word{3} ||
                  execution.dependency_barriers != exact::word{1};
  f += !o.inquiry.all_exact || !o.inquiry.source_separated ||
       !o.inquiry.comparison_withheld || !o.inquiry.alternatives_retained ||
       !o.inquiry.dependency_exact || !o.inquiry.theory_formed;
  f += o.inquiry.matching.injection_count[0] != 763 ||
       o.inquiry.matching.injection_count[1] != 763 ||
       !o.inquiry.matching.kronecker_exact ||
       !o.inquiry.matching.determinant_factored ||
       !o.inquiry.matching.independence_supported ||
       !o.inquiry.matching.duplicate_q_obstructed ||
       !o.inquiry.matching.changed_independence_undetermined ||
       o.inquiry.matching.p_vandermonde == 0 ||
       o.inquiry.matching.q_vandermonde == 0 ||
       o.inquiry.matching.duplicate_q_vandermonde != 0;
  for (std::uint8_t side = 0; side < 2; ++side)
    for (std::uint16_t slot = 0;
         slot < o.inquiry.matching.injection_count[side]; ++slot) {
      r30_reference_injection expected{};
      const auto &actual = w.injections[side][slot];
      f += !r30_reference_injection_at(side, slot, expected) ||
           actual.side != expected.side || actual.subset != expected.subset ||
           actual.forbidden != expected.forbidden ||
           actual.image[0] != expected.image[0] ||
           actual.image[1] != expected.image[1] ||
           actual.image[2] != expected.image[2] ||
           actual.size != expected.size || actual.weight != expected.weight ||
           actual.lineage !=
               exact::word{o.inquiry.matching_card.metadata.lineage.value() +
                           20'000U + static_cast<std::uint64_t>(side) * 1'000U +
                           slot};
    }
  for (std::uint8_t a = 0; a < 7; ++a)
    for (std::uint8_t b = 0; b < 7; ++b)
      for (std::uint8_t r = 0; r < 7; ++r)
        for (std::uint8_t c = 0; c < 7; ++c) {
          const auto slot =
              static_cast<std::size_t>(a * 7U + b) * 49U + r * 7U + c;
          const auto factor = r30_reference_factor_at(a, b);
          const auto &actual = w.jacobian[slot];
          const auto p = r30_reference_evaluation(0, a, c);
          const auto q = r30_reference_evaluation(1, b, r);
          f +=
              actual.alpha != a || actual.beta != b || actual.row != r ||
              actual.column != c || actual.p_size != factor.p_size ||
              actual.q_size != factor.q_size || actual.p_evaluation != p ||
              actual.q_evaluation != q ||
              actual.row_factor != factor.row_factor ||
              actual.value != r30_reference_jacobian(a, b, r, c) ||
              actual.value != factor.row_factor * p * q ||
              actual.lineage !=
                  exact::word{o.inquiry.matching_card.metadata.lineage.value() +
                              10'000U + slot};
        }
  for (std::uint8_t a = 0; a < 7; ++a)
    for (std::uint8_t b = 0; b < 7; ++b) {
      const auto slot = static_cast<std::size_t>(a * 7U + b);
      const auto expected = r30_reference_factor_at(a, b);
      const auto &actual = w.factors[slot];
      f += actual.alpha != a || actual.beta != b ||
           actual.p_size != expected.p_size ||
           actual.q_size != expected.q_size ||
           actual.p_leading != expected.p_leading ||
           actual.q_leading != expected.q_leading ||
           actual.row_factor != expected.row_factor || !actual.nonzero ||
           actual.lineage !=
               exact::word{o.inquiry.matching_card.metadata.lineage.value() +
                           30'000U + slot};
    }
  for (std::uint8_t p = 0; p < 4; ++p) {
    const auto &x = o.inquiry.polygons[p];
    f += x.double_area != ref.area[p] || x.boundary != ref.boundary[p] ||
         x.interior != ref.interior[p] || !x.pick_exact || !x.ehrhart_exact ||
         !x.reciprocity_exact || x.identity != exact::word{197'301U + p} ||
         x.lineage !=
             exact::word{o.inquiry.lattice_card.metadata.lineage.value() +
                         49'000U + p};
    for (std::uint8_t n = 0; n < 5; ++n)
      f += x.lattice_count[n] != ref.counts[p][n];
    for (std::uint8_t n = 0; n < 5; ++n)
      for (std::uint8_t px = 0; px < 21; ++px)
        for (std::uint8_t py = 0; py < 13; ++py) {
          const auto expected = r30_reference_lattice_point(p, n, px, py);
          const auto &actual = w.lattice[p][n][px][py];
          f += actual.in_box != expected.in_box ||
               actual.included != expected.included ||
               actual.boundary != expected.boundary;
          if (expected.in_box)
            f += actual.polygon != p || actual.dilation != n ||
                 actual.x != px || actual.y != py ||
                 actual.lineage !=
                     exact::word{
                         o.inquiry.lattice_card.metadata.lineage.value() +
                         50'000U + static_cast<std::uint64_t>(p) * 10'000U +
                         static_cast<std::uint64_t>(n) * 1'000U +
                         static_cast<std::uint64_t>(px) * 32U + py};
        }
  }
  const auto &potential = o.inquiry.potential;
  f += !potential.geometry_return_mounted || !potential.equations_exact ||
       !potential.eigen_exact || !potential.symbolic_minimum ||
       !potential.disconnected_obstructed || potential.solution[0] != 5 ||
       potential.solution[1] != 8 || potential.eigenvalues[0] != 3 ||
       potential.eigenvalues[1] != 5 || potential.disconnected_determinant != 0;
  constexpr std::int32_t matrix[4]{4, -1, -1, 4};
  constexpr std::int32_t boundary[2]{12, 27};
  constexpr std::int32_t characteristic[3]{1, -8, 15};
  constexpr std::int32_t eigenvectors[4]{1, 1, 1, -1};
  constexpr std::int32_t energy[3]{4, -2, 4};
  for (std::uint8_t i = 0; i < 4; ++i)
    f += potential.matrix[i] != matrix[i] ||
         potential.eigenvectors[i] != eigenvectors[i];
  for (std::uint8_t i = 0; i < 2; ++i)
    f += potential.boundary[i] != boundary[i];
  for (std::uint8_t i = 0; i < 3; ++i)
    f += potential.characteristic[i] != characteristic[i] ||
         potential.energy[i] != energy[i];
  f += o.inquiry.cover.subset_receipts != 70 ||
       o.inquiry.cover.pair_receipts != 64 ||
       !o.inquiry.cover.width_one_obstructed ||
       !o.inquiry.cover.width_two_obstructed ||
       !o.inquiry.cover.saturation_exact || !o.inquiry.cover.cover_exact;
  f += o.inquiry.cover.width_one_collision[0] ==
           o.inquiry.cover.width_one_collision[1] ||
       o.inquiry.cover.width_two_collision[0] ==
           o.inquiry.cover.width_two_collision[1] ||
       !o.inquiry.self_crossing_obstructed;
  for (std::uint8_t slot = 0; slot < 70; ++slot) {
    const auto expected = r30_reference_subset_at(slot);
    const auto &actual = w.subsets[slot];
    f += actual.columns[0] != expected.columns[0] ||
         actual.columns[1] != expected.columns[1] ||
         actual.columns[2] != expected.columns[2] ||
         actual.columns[3] != expected.columns[3] ||
         actual.witness_row != expected.witness ||
         actual.saturated != expected.saturated ||
         actual.lineage !=
             exact::word{o.inquiry.cover_card.metadata.lineage.value() +
                         70'000U + slot};
  }
  for (std::uint8_t slot = 0; slot < 64; ++slot) {
    const auto expected = r30_reference_pair_at(slot);
    const auto &actual = w.pairs[slot];
    f += actual.x != expected.x || actual.y != expected.y ||
         actual.witness != expected.witness || actual.left != expected.left ||
         actual.right != expected.right ||
         actual.lineage !=
             exact::word{o.inquiry.cover_card.metadata.lineage.value() +
                         71'000U + slot};
  }
  f += !o.foil.expected_rejection || o.foil.raw.exit_status == 0 ||
       o.foil.raw.stdout_bytes + o.foil.raw.stderr_bytes == 0 ||
       o.passage.typed.state != event::checker_return_status::accepted ||
       o.passage.raw.exit_status != 0 || o.passage.raw.stderr_bytes != 0 ||
       !contains(o.passage.formal.bytes, o.passage.formal.byte_count,
                 "theorem generated_plural_rederivation_ecology") ||
       !contains(o.passage.formal.bytes, o.passage.formal.byte_count,
                 "theorem generated_matching_nonzero_factors") ||
       !contains(o.passage.formal.bytes, o.passage.formal.byte_count,
                 "∀ x y : ℕ") ||
       !contains(o.passage.formal.bytes, o.passage.formal.byte_count,
                 "pairCertificate 7 7") ||
       contains(o.passage.formal.bytes, o.passage.formal.byte_count, "sorry") ||
       !contains(o.passage.conversational.bytes,
                 o.passage.conversational.byte_count,
                 "Exterior comparison remains withheld");
  f += o.foil.formation_commit.predecessor != exact::word{14'001'032} ||
       o.foil.returned_morphology.commit.successor != exact::word{14'001'034} ||
       o.passage.formation_commit.successor != exact::word{14'001'035} ||
       o.passage.returned_morphology.commit.successor !=
           exact::word{14'001'036} ||
       o.passage.returned_morphology.mathematical_after != 270 ||
       o.passage.returned_morphology.codec_after != 127;
  f += o.final_head != exact::word{14'001'036} ||
       o.final_continuation != exact::word{15'001'036} ||
       !o.final_can_continue ||
       h.integrity != event::rederivation_rest_integrity(h) ||
       h.body.regions[0].admitted_tally != 903 ||
       h.mathematical_admitted_tally != 270 || h.codec_admitted_tally != 127 ||
       h.arithmetic_spectral_admitted_tally != 47 ||
       h.rederivation_admitted_tally != 56 || !h.matching_rederivation.accepted ||
       !h.lattice_rederivation.accepted || !h.potential_rederivation.accepted ||
       !h.cover_rederivation.accepted;
  return f;
}
} // namespace holonics::tests
