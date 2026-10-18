import SRWTightness.PairShellCancellation

namespace SRWTightness

theorem pair_shell_exp_split (t f : ℝ) :
    Real.exp (-2 * t - 2 * f) = ((Real.exp t) ^ 2)⁻¹ * Real.exp (-2 * f) := by
  rw [show -2 * t - 2 * f = -(t + t) + (-2 * f) by ring,
    Real.exp_add, Real.exp_neg, Real.exp_add]
  congr 1
  ring

/-- The distance branch has exactly the inverse shell area needed for counting. -/
theorem pair_shell_distance_probability_scale (P C W t f a ρ B : ℝ)
    (hC : 0 ≤ C) (hW : 0 ≤ W) (ha : 0 < a) (hρ : 0 < ρ) (hB : 0 ≤ B)
    (hcover : a ≤ B * ρ)
    (hP : P ≤ (C / ρ ^ 2) * W * Real.exp (-2 * t - 2 * f)) :
    P ≤ (C * B ^ 2) / ((Real.exp t) ^ 2 * a ^ 2) * (W * Real.exp (-2 * f)) := by
  have hi := pair_shell_inverse_square a ρ B ha hρ hB hcover
  rw [pair_shell_exp_split] at hP
  have hh : (C * W) * (1 / ρ ^ 2) ≤ (C * W) * (B ^ 2 / a ^ 2) :=
    mul_le_mul_of_nonneg_left hi (mul_nonneg hC hW)
  have hh' := mul_le_mul_of_nonneg_right hh
    (show 0 ≤ ((Real.exp t) ^ 2)⁻¹ * Real.exp (-2 * f) by positivity)
  calc
    _ ≤ (C / ρ ^ 2) * W * (((Real.exp t) ^ 2)⁻¹ * Real.exp (-2 * f)) := hP
    _ = (C * W) * (1 / ρ ^ 2) * (((Real.exp t) ^ 2)⁻¹ * Real.exp (-2 * f)) := by ring
    _ ≤ (C * W) * (B ^ 2 / a ^ 2) * (((Real.exp t) ^ 2)⁻¹ * Real.exp (-2 * f)) := hh'
    _ = _ := by simp only [div_eq_mul_inv, _root_.mul_inv_rev]; ring

/-- The Chernoff branch has the same inverse shell area, using the actual logarithmic time error. -/
theorem pair_shell_chernoff_probability_scale (P C d t h f a E : ℝ)
    (hC : 0 ≤ C) (hd : 0 ≤ d) (ha : 0 < a) (he : |h - Real.log a| ≤ E)
    (hP : P ≤ C * d * Real.exp (-2 * t - 2 * h - 2 * f)) :
    P ≤ (C * Real.exp (2 * E)) / ((Real.exp t) ^ 2 * a ^ 2) *
      (d * Real.exp (-2 * f)) := by
  have hi := pair_shell_exp_scale a h E ha he
  have hs : Real.exp (-2 * t - 2 * h - 2 * f) =
      Real.exp (-2 * h) * Real.exp (-2 * t - 2 * f) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hs, pair_shell_exp_split] at hP
  have hh := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hi
      (show 0 ≤ ((Real.exp t) ^ 2)⁻¹ * Real.exp (-2 * f) by positivity)) (mul_nonneg hC hd)
  calc
    _ ≤ C * d * (Real.exp (-2 * h) * (((Real.exp t) ^ 2)⁻¹ * Real.exp (-2 * f))) := hP
    _ ≤ C * d * ((Real.exp (2 * E) / a ^ 2) *
        (((Real.exp t) ^ 2)⁻¹ * Real.exp (-2 * f))) := hh
    _ = _ := by simp only [div_eq_mul_inv, _root_.mul_inv_rev]; ring

end SRWTightness
