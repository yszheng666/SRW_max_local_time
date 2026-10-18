import SRWTightness.SourcePairDeficitDistance

namespace SRWTightness

/-- A single deterministic lower bound on A makes every retained source residual time large. -/
theorem source_pair_residual_time (b : Site) (t A C : ℝ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (hC : 0 ≤ C)
    (hlog : 4 * C + sourceEquilibriumTimeError + sourceLowerTimeError + 1 ≤ Real.log A)
    (I : ℕ)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (i : ℕ) (hi : i ≤ I) :
    0 < sourceLowerTime (sourceLowerRadius t) - sourceObservationTime t A I (I - i + 1) ∧
    4 * C ≤ sourceLowerTime (sourceLowerRadius t) - sourceObservationTime t A I (I - i + 1) := by
  have ha4 : 4 ≤ A := diskGaussianMinimumRadius_ge_four.trans
    (diskPointGaussianMinimumRadius_ge_base.trans hA)
  have hp : 1 ≤ diskEnergyGapRatio ^ i :=
    one_le_pow₀ (by linarith [diskEnergyGapRatio_gt_four])
  have hl := Real.log_le_log (by linarith : 0 < A)
    (show A ≤ A * diskEnergyGapRatio ^ i by nlinarith)
  have he := (abs_le.mp (source_pair_deficit_log_radius b t A hA ht I hI i hi)).1
  constructor <;> linarith

end SRWTightness
