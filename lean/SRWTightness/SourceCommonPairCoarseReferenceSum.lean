import SRWTightness.SourceCommonPairFullReferenceSum

open MeasureTheory Filter
open scoped BigOperators
namespace SRWTightness

/-- Manuscript (7.29), the lower cutoff used for later common coarse endpoints. -/
noncomputable def sourceCoarseLowerLevel (t : ℝ) : ℕ :=
  ⌈(1000 * Real.log t) ^ (5 / 2 : ℝ)⌉₊

/-- The manuscript lower cutoff eventually exceeds the fixed endpoint-estimate threshold. -/
theorem sourceCoarseLowerLevel_eventually_twenty :
    ∀ᶠ t : ℝ in atTop, 20 ≤ sourceCoarseLowerLevel t := by
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with t ht
  have hx : 1 ≤ 1000 * Real.log t := by linarith
  have hp := Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (1 : ℝ) ≤ 5 / 2)
  rw [Real.rpow_one] at hp
  have hc := Nat.le_ceil ((1000 * Real.log t) ^ (5 / 2 : ℝ))
  have h : (20 : ℝ) ≤ (sourceCoarseLowerLevel t : ℝ) := by
    change (20 : ℝ) ≤ (⌈(1000 * Real.log t) ^ (5 / 2 : ℝ)⌉₊ : ℝ)
    linarith
  exact_mod_cast h

/-- All permitted population states, including zero, obey the source reference estimate. -/
theorem source_common_pair_coarse_reference_sum
    (hGW : GeometricGWOneRootMarginalInput)
    (hOcc : FiniteOccupationRowIntegrabilityInput) (hRes : FiniteResolventRowBoundInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (j : ℕ), b ≠ w → sourceCoarseLowerLevel t ≤ j →
      j + sourceCommonPairGap t = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      ∀ (hpair : ({b, w} : Finset Site) ⊆ sourceCommonPairObservation b w),
      (∑ k ∈ Finset.range (⌊(sourceCommonPairEndpoint t j) ^ 2 / 2⌋₊ + 1),
        (geometricGWRecordLaw 1 j).real {r | geometricGWPopulation r j = k} *
        (markProductLaw (sourceCommonPairDomain t b j) (sourceCommonPairObservation b w) (sourceCommonPairIntensity t j) k).real
          {Y | ∀ v : ({b, w} : Finset Site), (2 / Real.pi) * (sourceTerminalHeight t) ^ 2 / 2 ≤
            (sumMarks (sourceCommonPairObservation b w) k Y ⟨v, hpair v.property⟩ : ℝ)}) ≤
        C * t ^ 2 * Real.exp (-(sourceCommonPairEndpoint t j) ^ 2 / (2 * ((j : ℝ) + 1)) -
          (sourceTerminalHeight t - sourceCommonPairEndpoint t j) ^ 2 / sourceCommonPairRowScale t b w j) := by
  obtain ⟨C, hC, hbound⟩ := source_common_pair_full_reference_sum hGW hOcc hRes
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound, sourceCoarseLowerLevel_eventually_twenty] with t ht hcut
  intro b w j hbw hj hindex hdepth hpair
  exact ht b w j hbw (hcut.trans hj) hindex hdepth hpair

end SRWTightness
