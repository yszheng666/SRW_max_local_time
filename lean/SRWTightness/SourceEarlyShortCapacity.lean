import SRWTightness.BufferedAnnulusCapacity
import SRWTightness.SourceEarlyCommonIntensity

open Filter
namespace SRWTightness

/-- Equation 8.15 with a uniform error for every short annulus in the early range. -/
theorem source_early_short_capacity (hinput : PotentialKernelAsymptoticInput) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ᶠ t : ℝ in atTop, ∀ ν : ℕ,
      ν ≤ 2 * sourceCoarseLowerLevel t → ∀ b : Site,
      ∃ δ : ℝ, |δ| ≤ L / sourceCommonPairInnerRadius t ν ∧
        capacity
          (sourceExitDomain (sourceLowerRadius t) 1
            (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) b ν)
          (sourceEntranceDomain (sourceLowerRadius t) 1
            (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) b ν) =
        ((2 / Real.pi) * Real.log
          ((sourceRecordRadius (sourceLowerRadius t)
            (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) ν + 14) /
            (sourceCommonPairInnerRadius t ν - 14)) + δ)⁻¹ := by
  obtain ⟨L, T, hL, hT, hc⟩ := buffered_annulus_capacity hinput
  refine ⟨L, hL, ?_⟩
  filter_upwards [source_early_level_bounds,
    sourceLowerRadius_tendsto_atTop.eventually (eventually_ge_atTop (max T 28))]
    with t ht hm
  intro ν hν b
  have hr := hm.trans (sourceCommonPairInnerRadius_ge_lower t ν (ht.2 ν hν).1)
  have hT' := (le_max_left T 28).trans hr
  have h28 := (le_max_right T 28).trans hr
  obtain ⟨δ, hδ, heq⟩ := hc (sourceCommonPairInnerRadius t ν) 14 hT'
    (by norm_num) (by linarith) b
  refine ⟨δ, hδ, ?_⟩
  simpa only [sourceCommonPairInnerRadius, sourceRecordRadius_successor,
    sourceExitDomain, sourceEntranceDomain, sourceRecordBuffer,
    show (4 : ℝ) * 1 + 10 = 14 by norm_num] using heq

end SRWTightness
