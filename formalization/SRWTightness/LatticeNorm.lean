import SRWTightness.StepBound
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace SRWTightness

theorem normSq_neg (z : Site) : normSq (-z) = normSq z := by
  simp [normSq]

theorem normSq_eq_zero_iff (z : Site) : normSq z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have h1 : (z.1 : ℝ) ^ 2 = 0 := by unfold normSq at h; nlinarith [sq_nonneg (z.2 : ℝ)]
    have h2 : (z.2 : ℝ) ^ 2 = 0 := by unfold normSq at h; nlinarith [sq_nonneg (z.1 : ℝ)]
    apply Prod.ext
    · exact_mod_cast (eq_zero_of_pow_eq_zero h1)
    · exact_mod_cast (eq_zero_of_pow_eq_zero h2)
  · rintro rfl
    simp [normSq]

theorem one_le_normSq_of_ne_zero (z : Site) (hz : z ≠ 0) : 1 ≤ normSq z := by
  have hp : 0 < normSq z := lt_of_le_of_ne (normSq_nonneg z) (Ne.symm ((normSq_eq_zero_iff z).not.mpr hz))
  unfold normSq at hp ⊢
  have hi : (0 : ℤ) < z.1 ^ 2 + z.2 ^ 2 := by exact_mod_cast hp
  have hi1 : (1 : ℤ) ≤ z.1 ^ 2 + z.2 ^ 2 := by omega
  exact_mod_cast hi1

theorem normSq_eq_sq_sqrt (z : Site) : normSq z = (Real.sqrt (normSq z)) ^ 2 :=
  (Real.sq_sqrt (normSq_nonneg z)).symm

end SRWTightness
