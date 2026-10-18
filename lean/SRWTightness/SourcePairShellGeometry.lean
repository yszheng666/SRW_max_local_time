import SRWTightness.SourcePairShellSpacing
import SRWTightness.SourcePairDeficitDistance
import SRWTightness.PairShellCancellation
import SRWTightness.TimeGridInterpolation

namespace SRWTightness

/-- All actual shell deficits stay in [1,d], and their number is at most d. -/
theorem source_pair_shell_deficit_bounds (t A : ℝ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (hlog : sourceEquilibriumTimeError + sourceLowerTimeError + 1 ≤ Real.log A)
    (I : ℕ)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I) :
    (∀ i ≤ I, 1 ≤ sourceLowerTime (sourceLowerRadius t) -
      sourceObservationTime t A I (I - i + 1) ∧
      sourceLowerTime (sourceLowerRadius t) - sourceObservationTime t A I (I - i + 1) ≤
        sourceLowerTime (sourceLowerRadius t)) ∧
    (I + 1 : ℝ) ≤ sourceLowerTime (sourceLowerRadius t) := by
  have ha4 : 4 ≤ A := diskGaussianMinimumRadius_ge_four.trans
    (diskPointGaussianMinimumRadius_ge_base.trans hA)
  have hg := sourceObservationTime_gaps t A hA ht I hI
  have hb (i : ℕ) (hi : i ≤ I) : 1 ≤ sourceLowerTime (sourceLowerRadius t) -
      sourceObservationTime t A I (I - i + 1) ∧
      sourceLowerTime (sourceLowerRadius t) - sourceObservationTime t A I (I - i + 1) ≤
        sourceLowerTime (sourceLowerRadius t) := by
    have hp : 1 ≤ diskEnergyGapRatio ^ i :=
      one_le_pow₀ (by linarith [diskEnergyGapRatio_gt_four])
    have hl := Real.log_le_log (by linarith : 0 < A)
      (show A ≤ A * diskEnergyGapRatio ^ i by nlinarith)
    have he := (abs_le.mp (source_pair_deficit_log_radius 0 t A hA ht I hI i hi)).1
    have hn := timeGridTime_mono (sourceObservationTime t A I) (I + 2)
      (fun j hj ↦ by have hh := hg j (by omega); linarith) (Nat.zero_le (I - i + 1))
      (show I - i + 1 ≤ I + 2 by omega)
    rw [sourceObservationTime_zero] at hn
    constructor <;> linarith
  refine ⟨hb, ?_⟩
  have hi : ∀ i ≤ I, (i + 1 : ℝ) ≤ sourceLowerTime (sourceLowerRadius t) -
      sourceObservationTime t A I (I - i + 1) := by
    intro i
    induction i with
    | zero => intro h; simpa using (hb 0 h).1
    | succ i ih =>
      intro h
      have hh := ih (by omega)
      have hg := source_pair_shell_deficit_gap t A hA ht I hI i (by omega)
      push_cast
      linarith
  exact (hi I le_rfl).trans (hb I le_rfl).2

/-- The inverse shell radius square is obtained directly from the actual node time. -/
theorem source_pair_shell_exp_scale (t A : ℝ)
    (hA : diskPointGaussianMinimumRadius ≤ A) (ht : sourceGaussianThreshold A ≤ t)
    (I : ℕ)
    (hI : ∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I)
    (i : ℕ) (hi : i ≤ I) :
    Real.exp (-2 * (sourceLowerTime (sourceLowerRadius t) -
      sourceObservationTime t A I (I - i + 1))) ≤
      Real.exp (2 * (sourceEquilibriumTimeError + sourceLowerTimeError)) /
        (A * diskEnergyGapRatio ^ i) ^ 2 := by
  have ha4 : 4 ≤ A := diskGaussianMinimumRadius_ge_four.trans
    (diskPointGaussianMinimumRadius_ge_base.trans hA)
  apply pair_shell_exp_scale
  · exact mul_pos (by linarith) (pow_pos (by linarith [diskEnergyGapRatio_gt_four]) _)
  · exact source_pair_deficit_log_radius 0 t A hA ht I hI i hi

end SRWTightness
