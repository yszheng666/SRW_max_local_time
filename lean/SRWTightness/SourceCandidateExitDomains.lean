import SRWTightness.SourceForestApplicationGeometry
import SRWTightness.SourceCandidateAnnulus
import SRWTightness.RootOuterDomainGeometry

open Filter
namespace SRWTightness

/-- Every source exit domain around a candidate center lies in the original killing disk. -/
theorem source_candidate_exit_domains :
    ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceCandidateAnnulus (Real.exp t), ∀ k : ℕ,
      sourceExitDomain (sourceLowerRadius t) 1
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) b k ⊆ diskFinset (Real.exp t) := by
  obtain ⟨T, hT⟩ := source_outer_scale_large
  filter_upwards [eventually_ge_atTop T,
    sourceLowerRadius_tendsto_atTop.eventually (eventually_ge_atTop (70 : ℝ))] with t ht hm
  intro b hb k
  have hscale : 32 * sourceLowerRadius t ≤ Real.exp t := by
    have hh := (hT t ht).2
    nlinarith [Real.exp_one_gt_two, sourceLowerRadius_pos t]
  have hbc := (mem_sourceCandidateAnnulus (Real.exp t) (Real.exp_pos _) b).mp hb
  have hfit := (source_annular_center_geometry (Real.exp t) (sourceLowerRadius t)
    hm hscale b hbc.1 hbc.2 k).2
  have hc : 0 ≤ sourceRecordRadius (sourceLowerRadius t)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) k + 14 := by
    unfold sourceRecordRadius
    positivity
  have hh := (root_domain_and_exit_inside b _ (Real.exp t) hc hfit).1
  simpa only [sourceExitDomain, sourceRecordBuffer, mul_one,
    show (4 : ℝ) + 10 = 14 by norm_num] using hh

end SRWTightness
