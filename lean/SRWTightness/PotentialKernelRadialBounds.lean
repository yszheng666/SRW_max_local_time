import SRWTightness.PotentialKernelLogGrowth
import SRWTightness.LatticeNorm

namespace SRWTightness

noncomputable def potentialUpperConstant : ℝ := 1 + 1 / Real.pi + 2 * Real.pi
noncomputable def potentialLowerConstant : ℝ := 2 + 16 * Real.exp 1 / Real.pi

theorem potentialUpperConstant_pos : 0 < potentialUpperConstant := by
  unfold potentialUpperConstant
  positivity

theorem potentialLowerConstant_pos : 0 < potentialLowerConstant := by
  unfold potentialLowerConstant
  positivity

theorem potentialKernel_le_log_normBound (z : Site) (B : ℝ) (hB : 1 ≤ B) (hz : normSq z ≤ B) :
    potentialKernel z ≤ Real.log B / Real.pi + potentialUpperConstant := by
  by_cases hz0 : z = 0
  · subst z
    rw [potentialKernel_zero]
    exact add_nonneg (div_nonneg (Real.log_nonneg hB) Real.pi_pos.le) potentialUpperConstant_pos.le
  · have h := potentialKernel_log_upper z (one_le_normSq_of_ne_zero z hz0)
    have hlog : Real.log (normSq z) ≤ Real.log B :=
      Real.log_le_log (by have := one_le_normSq_of_ne_zero z hz0; linarith) hz
    have hl := div_le_div_of_nonneg_right hlog Real.pi_pos.le
    unfold potentialUpperConstant
    linarith

theorem potentialKernel_ge_log_radius (z : Site) :
    (2 / Real.pi) * Real.log (max (Real.sqrt (normSq z)) 1) - potentialLowerConstant ≤ potentialKernel z := by
  by_cases hz0 : z = 0
  · subst z
    simp only [normSq, Prod.fst_zero, Prod.snd_zero, Int.cast_zero, zero_pow (by omega : 2 ≠ 0),
      zero_add, Real.sqrt_zero, max_eq_right (by norm_num : (0 : ℝ) ≤ 1), Real.log_one, mul_zero,
      zero_sub, potentialKernel_zero]
    linarith [potentialLowerConstant_pos]
  · have hz := one_le_normSq_of_ne_zero z hz0
    rw [max_eq_left (Real.one_le_sqrt.mpr hz), Real.log_sqrt (normSq_nonneg z)]
    have h := potentialKernel_log_lower z hz
    unfold potentialLowerConstant
    calc
      _ = Real.log (normSq z) / Real.pi - (2 + 16 * Real.exp 1 / Real.pi) := by ring
      _ ≤ _ := h

end SRWTightness
