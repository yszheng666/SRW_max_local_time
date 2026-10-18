import SRWTightness.SourceObservationTime
import SRWTightness.SourceFinalIncrementVariance

namespace SRWTightness

/-- Actual source cutoff and final variance lie in fixed ranges determined only by A. -/
theorem source_terminal_cutoff_range (b : Site) (t A : ℝ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (I : ℕ)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I) :
    |(sourceLowerTime (sourceLowerRadius t) - sourceObservationTime t A I (I + 1)) -
      Real.log A| ≤ sourceEquilibriumTimeError + sourceLowerTimeError ∧
    1 ≤ sourceObservationTime t A I (I + 2) - sourceObservationTime t A I (I + 1) ∧
    sourceObservationTime t A I (I + 2) - sourceObservationTime t A I (I + 1) ≤
      Real.log A + sourcePointEnergyTimeError + sourceEquilibriumTimeError := by
  have ha4 : 4 ≤ A := diskGaussianMinimumRadius_ge_four.trans
    (diskPointGaussianMinimumRadius_ge_base.trans hA)
  have htbase : sourceScaleThreshold A ≤ t := (le_max_left _ _).trans ht
  obtain ⟨ht2, hcut, hm70, _⟩ := sourceScaleThreshold_conditions t A ha4 htbase
  have ht6 : (2 : ℝ) ≤ t ^ 6 := ht2.trans (by
    simpa using pow_le_pow_right₀ (by linarith : 1 ≤ t) (by norm_num : 1 ≤ 6))
  have hcut' := (le_div_iff₀ (by positivity : 0 < t ^ 6)).mp hcut
  have hma : 2 * A ≤ sourceLowerRadius t := by
    nlinarith [mul_le_mul_of_nonneg_left ht6 (by linarith : 0 ≤ A)]
  have he := sourceEquilibriumTime_lowerTime_bound b (sourceLowerRadius t) A 14
    (by linarith) hma (by norm_num) (by linarith)
  have hv := source_final_increment_variance_log_bound b (sourceLowerRadius t) A 14
    (by linarith) hma (by norm_num) (by linarith)
  have hg := sourceObservationTime_gaps t A hA ht I hI (I + 1) (by omega)
  refine ⟨?_, by simpa only [Nat.add_assoc] using hg, ?_⟩
  · rw [sourceObservationTime_last_average b]
    have hh : (sourceLowerTime (sourceLowerRadius t) -
        sourceEquilibriumTime b (sourceLowerRadius t) A 14) - Real.log A =
        -(sourceEquilibriumTime b (sourceLowerRadius t) A 14 -
          (sourceLowerTime (sourceLowerRadius t) - Real.log A)) := by ring
    rw [hh, abs_neg]
    exact he
  · rw [sourceObservationTime_site b, sourceObservationTime_last_average b]
    linarith [(abs_le.mp hv).2]

end SRWTightness
