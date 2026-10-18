import SRWTightness.SourceCommonSignedGeometry
import SRWTightness.SourceCommonPairDistanceChernoff
import SRWTightness.SourceScaleThreshold
import SRWTightness.SourceCommonPairRadiusLower

open Filter

namespace SRWTightness

/-- The literal common level eventually supplies all two-site mark geometry and normalization. -/
theorem source_common_literal_mark_geometry :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (j : ℕ), b ≠ w →
      (j : ℤ) = sourceSignedCommonPairLevel t (Real.sqrt (normSq (w - b))) →
      j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      let a := 2 * Real.sqrt (normSq (w - b))
      let m := sourceCommonPairInnerRadius t j
      1 ≤ a ∧ 2 * a ≤ m ∧ 70 ≤ m ∧
      diskGreenEnergyConstant / (2 / Real.pi) + Real.log 4 + 4 ≤ Real.log m - Real.log a ∧
      0 ≤ sourceCommonPairIntensity t j ∧
      sourceCommonPairIntensity t j *
        capacity (sourceCommonPairDomain t b j) (sourceCommonPairObservation b w) ≤ 1 := by
  let A := Real.log 4 + 1
  let E := diskGreenEnergyConstant / (2 / Real.pi) + Real.log 4 + 4 + Real.log 2 + 1
  filter_upwards [eventually_ge_atTop (sourceScaleThreshold 4),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 (max A E)))] with t ht hl
  have hscale := sourceScaleThreshold_conditions t 4 (by norm_num) ht
  have ht1 : 1 ≤ t := by linarith [hscale.1]
  have hlog1 : 1 ≤ Real.log t := (le_max_left _ _).trans hl
  have hA : A ≤ Real.log t := (le_max_left _ _).trans ((le_max_right _ _).trans hl)
  have hE : E ≤ Real.log t := (le_max_right _ _).trans ((le_max_right _ _).trans hl)
  have hg := (sourceCommonPairGap_bounds t ht1).1
  intro b w j hbw hj hd
  obtain ⟨hρ, ho, hi⟩ := source_common_signed_pair_geometry t b w j ht1 hbw hj
  have hp : 0 < Real.sqrt (normSq (w - b)) := by linarith
  have hs := source_common_pair_observation_separation t _ hp ho j (sourceCommonPairGap t) hi
    (show A ≤ (sourceCommonPairGap t : ℝ) by linarith)
    (show E ≤ (sourceCommonPairGap t : ℝ) by linarith)
  have hm := hscale.2.2.1.trans (sourceCommonPairInnerRadius_ge_lower t j hd)
  have hα := (sourceCommonPairIntensity_bounds t j hm).1.le
  refine ⟨by linarith, hs.1, hm, hs.2, hα, ?_⟩
  rw [sourceCommonPairDomain_eq]
  exact (source_terminal_capacity_half b (sourceCommonPairInnerRadius t j) 14
    (2 * Real.sqrt (normSq (w - b))) (sourceCommonPairObservation b w)
    (by linarith) hs.1 (by norm_num) (by linarith) (Finset.Subset.refl _) hs.2).trans
      (by norm_num)

end SRWTightness
