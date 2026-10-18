import SRWTightness.SourcePairObservationTime

namespace SRWTightness

/-- The actual maximal source cutoff discharges all geometric premises of the node deficit estimate. -/
theorem source_pair_deficit_log_radius (b : Site) (t A : ℝ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (I : ℕ)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (i : ℕ) (hi : i ≤ I) :
    |(sourceLowerTime (sourceLowerRadius t) - sourceObservationTime t A I (I - i + 1)) -
      Real.log (A * diskEnergyGapRatio ^ i)| ≤
        sourceEquilibriumTimeError + sourceLowerTimeError := by
  have ha4 : 4 ≤ A := diskGaussianMinimumRadius_ge_four.trans
    (diskPointGaussianMinimumRadius_ge_base.trans hA)
  have htbase : sourceScaleThreshold A ≤ t := (le_max_left _ _).trans ht
  obtain ⟨ht2, hcut, hm70, hrest⟩ := sourceScaleThreshold_conditions t A ha4 htbase
  have hp : 1 ≤ diskEnergyGapRatio ^ i :=
    one_le_pow₀ (by linarith [diskEnergyGapRatio_gt_four])
  have ha : 1 ≤ A * diskEnergyGapRatio ^ i := by nlinarith
  have ht6 : (2 : ℝ) ≤ t ^ 6 := ht2.trans (by
    simpa using pow_le_pow_right₀ (by linarith : 1 ≤ t) (by norm_num : 1 ≤ 6))
  have hmul := (le_div_iff₀ (by positivity : 0 < t ^ 6)).mp ((hI i).mpr hi)
  have hma : 2 * (A * diskEnergyGapRatio ^ i) ≤ sourceLowerRadius t := by nlinarith
  exact source_pair_node_deficit_log_radius b t A I i hi ha hma hm70

/-- A covering observation radius gives the manuscript h=log ρ+O(1), uniformly in the distance. -/
theorem source_pair_deficit_log_distance (b : Site) (t A ρ : ℝ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (I : ℕ)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (i : ℕ) (hi : i ≤ I) (hρ : 0 < ρ)
    (hlo : 4 * ρ ≤ A * diskEnergyGapRatio ^ i)
    (hhi : A * diskEnergyGapRatio ^ i ≤ 4 * diskEnergyGapRatio * ρ) :
    |(sourceLowerTime (sourceLowerRadius t) - sourceObservationTime t A I (I - i + 1)) -
      Real.log ρ| ≤ sourceEquilibriumTimeError + sourceLowerTimeError +
        Real.log (4 * diskEnergyGapRatio) := by
  have he := abs_le.mp (source_pair_deficit_log_radius b t A hA ht I hI i hi)
  have ha : 0 < A * diskEnergyGapRatio ^ i := by linarith
  have hl := Real.log_le_log hρ (show ρ ≤ A * diskEnergyGapRatio ^ i by linarith)
  have hu := Real.log_le_log ha hhi
  have hB := diskEnergyGapRatio_gt_four
  rw [Real.log_mul (by positivity : 4 * diskEnergyGapRatio ≠ 0) hρ.ne'] at hu
  have hlog : 0 ≤ Real.log (4 * diskEnergyGapRatio) := Real.log_nonneg (by linarith)
  apply abs_le.mpr
  constructor <;> linarith

end SRWTightness
