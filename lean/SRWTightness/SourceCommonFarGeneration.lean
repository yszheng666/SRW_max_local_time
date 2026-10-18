import SRWTightness.SourceCommonDistanceRange
import SRWTightness.SourcePairShellCover

namespace SRWTightness

/-- The maximal retained observation radius gives the source far-pair generation bound. -/
theorem source_far_distance_index (t A ρ : ℝ) (I : ℕ) (ht : 1 ≤ t) (hA : 0 < A)
    (hρ : 0 < ρ)
    (hI : ∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I)
    (hsep : A * diskEnergyGapRatio ^ I / (8 * diskEnergyGapRatio) < ρ)
    :
    (sourceCommonPairDistanceIndex t ρ : ℝ) ≤ (sourceRootDepth (Real.exp t) (sourceLowerRadius t) : ℝ) +
      6 * Real.log t + Real.log (8 * diskEnergyGapRatio ^ 2) := by
  have ht0 : 0 < t := by linarith
  have hB : 0 < diskEnergyGapRatio := by linarith [diskEnergyGapRatio_gt_four]
  have hm := sourceLowerRadius_pos t
  have hnext : sourceLowerRadius t / t ^ 6 < A * diskEnergyGapRatio ^ (I + 1) := by
    apply lt_of_not_ge
    intro hh
    have hh' := (hI (I + 1)).mp hh
    omega
  rw [pow_succ diskEnergyGapRatio I, ← mul_assoc] at hnext
  have hmupper := (div_lt_iff₀ (by positivity : 0 < t ^ 6)).mp hnext
  have hamax := (div_lt_iff₀ (by positivity : 0 < 8 * diskEnergyGapRatio)).mp hsep
  have hprod := mul_lt_mul_of_pos_right hamax
    (by positivity : 0 < diskEnergyGapRatio * t ^ 6)
  have hratio : sourceLowerRadius t / ρ < 8 * diskEnergyGapRatio ^ 2 * t ^ 6 := by
    apply (div_lt_iff₀ hρ).mpr
    calc
      sourceLowerRadius t < (A * diskEnergyGapRatio ^ I * diskEnergyGapRatio) * t ^ 6 := hmupper
      _ = (A * diskEnergyGapRatio ^ I) * (diskEnergyGapRatio * t ^ 6) := by ring
      _ < (ρ * (8 * diskEnergyGapRatio)) * (diskEnergyGapRatio * t ^ 6) := hprod
      _ = _ := by ring
  have hlog := Real.log_lt_log (div_pos hm hρ) hratio
  rw [Real.log_mul (by positivity : 8 * diskEnergyGapRatio ^ 2 ≠ 0) (by positivity : t ^ 6 ≠ 0),
    Real.log_pow] at hlog
  let r := sourceRecordRadius (sourceLowerRadius t)
    (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) 0
  have hr : 0 < r := by dsimp [r, sourceRecordRadius]; positivity
  by_cases ha : sourceCommonPairDistanceIndex t ρ = 0
  · rw [ha, Nat.cast_zero]
    have hl := Real.log_nonneg ht
    have hc : 0 ≤ Real.log (8 * diskEnergyGapRatio ^ 2) := by
      apply Real.log_nonneg
      nlinarith [diskEnergyGapRatio_gt_four]
    positivity
  have ha1 : 1 ≤ sourceCommonPairDistanceIndex t ρ := by omega
  have hl1 : 1 ≤ Real.log (r / ρ) := (Nat.one_le_floor_iff _).mp ha1
  have hf := Nat.floor_le (show 0 ≤ Real.log (r / ρ) by linarith)
  change (sourceCommonPairDistanceIndex t ρ : ℝ) ≤ Real.log (r / ρ) at hf
  have hid : Real.log (r / ρ) = Real.log (sourceLowerRadius t / ρ) +
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t) : ℝ) := by
    dsimp [r, sourceRecordRadius]
    rw [Real.log_div (by positivity) hρ.ne', Real.log_mul hm.ne' (Real.exp_pos _).ne',
      Real.log_exp, Real.log_div hm.ne' hρ.ne']
    simp only [Nat.cast_zero, sub_zero]
    ring
  rw [hid] at hf
  linarith

/-- A nonnegative common level inherits the far-pair distance-index bound. -/
theorem source_common_far_generation (t A ρ : ℝ) (I j : ℕ) (ht : 1 ≤ t) (hA : 0 < A)
    (hρ : 0 < ρ)
    (hI : ∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I)
    (hsep : A * diskEnergyGapRatio ^ I / (8 * diskEnergyGapRatio) < ρ)
    (hi : j + sourceCommonPairGap t = sourceCommonPairDistanceIndex t ρ) :
    (j : ℝ) ≤ (sourceRootDepth (Real.exp t) (sourceLowerRadius t) : ℝ) +
      6 * Real.log t + Real.log (8 * diskEnergyGapRatio ^ 2) - (sourceCommonPairGap t : ℝ) := by
  have hh := source_far_distance_index t A ρ I ht hA hρ hI hsep
  have hc : (j : ℝ) + (sourceCommonPairGap t : ℝ) =
      (sourceCommonPairDistanceIndex t ρ : ℝ) := by exact_mod_cast hi
  linarith

end SRWTightness
