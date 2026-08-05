#include "r30_artifact.hpp"
#include <ostream>
namespace holonics::tests {
void write_r30_artifact(std::ostream &out, bool loaded,
                        const apparatus::rederivation_store_receipt (&cards)[3],
                        const apparatus::rederivation_store_receipt &rest_load,
                        const apparatus::rederivation_store_receipt &rest_write,
                        const apparatus::rederivation_executor_receipt &e,
                        const event::rederivation_observation &o,
                        const event::rederivation_rest_record &h,
                        std::size_t failures) {
  out << "truth_status=established-bounded\nevidence=implemented-exact,"
         "computational-witness\n"
      << "formal_truth_status=proved-derived\nformal_evidence=formal-checked\n"
      << "released_asymptotic_theorems_status=outside-aperture\nprogram=r30_"
         "plural_rederivation.sm_"
      << e.device_major << e.device_minor
      << "\ndevice_compute_capability=" << e.device_major << '.'
      << e.device_minor << "\nkernel_launches=" << e.kernel_launches.value()
      << "\nlaunched_threads=" << e.launched_threads.value()
      << "\nsemantic_threads=" << e.semantic_threads.value()
      << "\nhost_semantic_events=" << e.host_semantic_events.value()
      << "\nsource_currents=" << e.source_currents.value()
      << "\ndependency_barriers=" << e.dependency_barriers.value()
      << "\nverification_failures=" << failures
      << "\nexecutor_state=" << static_cast<unsigned>(e.state)
      << "\nsource_cards=loaded:" << loaded
      << ",bytes:" << cards[0].bytes.value() << ',' << cards[1].bytes.value()
      << ',' << cards[2].bytes.value() << ",distinct_paths:"
      << (cards[0].path_fold != cards[1].path_fold &&
          cards[0].path_fold != cards[2].path_fold &&
          cards[1].path_fold != cards[2].path_fold)
      << "\npredecessor_remount=body:" << o.predecessor_remount.body.returned
      << ",same_body:" << o.predecessor_remount.same_body
      << ",theory:" << o.predecessor_remount.theory_preserved
      << ",source_replayed:" << o.predecessor_remount.source_replayed
      << "\nmatching=coefficients:" << o.inquiry.matching.coefficient_count
      << ",jacobian:" << o.inquiry.matching.jacobian_entries << ",injections:"
      << o.inquiry.matching.injection_count[0] +
             o.inquiry.matching.injection_count[1]
      << ",factor:" << o.inquiry.matching.determinant_factored
      << ",vandermonde:" << o.inquiry.matching.p_vandermonde << ','
      << o.inquiry.matching.q_vandermonde
      << ",duplicate_vandermonde:" << o.inquiry.matching.duplicate_q_vandermonde
      << ",duplicate_obstruction:" << o.inquiry.matching.duplicate_q_obstructed;
  for (std::uint8_t p = 0; p < 4; ++p) {
    const auto &x = o.inquiry.polygons[p];
    out << "\npolygon_" << static_cast<unsigned>(p)
        << "=area2:" << x.double_area << ",boundary:" << x.boundary
        << ",interior:" << x.interior << ",counts:" << x.lattice_count[0] << ','
        << x.lattice_count[1] << ',' << x.lattice_count[2] << ','
        << x.lattice_count[3] << ',' << x.lattice_count[4]
        << ",exact:" << x.pick_exact << x.ehrhart_exact << x.reciprocity_exact;
  }
  out << "\npotential=matrix:4,-1,-1,4,section:"
      << o.inquiry.potential.solution[0] << ','
      << o.inquiry.potential.solution[1]
      << ",eigen:3,5,energy:" << o.inquiry.potential.symbolic_minimum
      << ",dependency:" << o.inquiry.potential.geometry_return_mounted
      << ",disconnected_determinant:"
      << o.inquiry.potential.disconnected_determinant
      << "\ncover=width:" << static_cast<unsigned>(o.inquiry.cover.width)
      << ",subsets:" << static_cast<unsigned>(o.inquiry.cover.subset_receipts)
      << ",pairs:" << static_cast<unsigned>(o.inquiry.cover.pair_receipts)
      << ",exact:" << o.inquiry.cover.cover_exact << ",collisions:"
      << static_cast<unsigned>(o.inquiry.cover.width_one_collision[0]) << '-'
      << static_cast<unsigned>(o.inquiry.cover.width_one_collision[1]) << ','
      << static_cast<unsigned>(o.inquiry.cover.width_two_collision[0]) << '-'
      << static_cast<unsigned>(o.inquiry.cover.width_two_collision[1])
      << ",self_crossing:" << o.inquiry.self_crossing_obstructed
      << "\nfoil_checker=exit:" << o.foil.raw.exit_status
      << ",stdout_bytes:" << o.foil.raw.stdout_bytes
      << ",stderr_bytes:" << o.foil.raw.stderr_bytes
      << ",expected_rejection:" << o.foil.expected_rejection
      << "\nvalid_checker=exit:" << o.passage.raw.exit_status
      << ",stdout_bytes:" << o.passage.raw.stdout_bytes
      << ",stderr_bytes:" << o.passage.raw.stderr_bytes
      << ",produced_bytes:" << o.passage.raw.produced_artifact_bytes
      << "\nfinal_body=head:" << o.final_head.value()
      << ",continuation:" << o.final_continuation.value()
      << ",morphology:" << h.body.regions[0].morphology
      << ",mathematical:" << h.mathematical_morphology
      << ",codec:" << h.codec_morphology
      << ",arithmetic:" << h.arithmetic_spectral_morphology
      << ",rederivation:" << h.rederivation_morphology
      << ",rest_bytes:" << sizeof(h) << ",integrity:" << h.integrity
      << "\nfinal_rest=returned:" << o.rest.returned
      << ",prior:" << o.rest.prior_returns_preserved
      << ",detached:" << o.rest.source_detached
      << ",remount_body:" << o.remount.body.returned
      << ",remount_same:" << o.remount.same_body
      << ",remount_theory:" << o.remount.theory_preserved
      << ",remount_replay:" << o.remount.source_replayed
      << ",handoff:" << o.handoff.returned
      << ",can_continue:" << o.final_can_continue
      << "\nrest_io=loaded:" << rest_load.returned()
      << ",written:" << rest_write.returned()
      << "\nphysical_telemetry=engine_time:unknown,checker_time:unknown,"
         "temperature:unknown,power:unknown,energy:unknown\n"
      << "formal_begin\n";
  out.write(o.passage.formal.bytes, o.passage.formal.byte_count);
  out << "formal_end\nfoil_begin\n";
  out.write(o.foil.formal.bytes, o.foil.formal.byte_count);
  out << "foil_end\nconversation_begin\n";
  out.write(o.passage.conversational.bytes,
            o.passage.conversational.byte_count);
  out << "\nconversation_end\n";
}
} // namespace holonics::tests
