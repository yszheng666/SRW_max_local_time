import SRWTightness.PlanarGaussianShiftedTail
import SRWTightness.ExternalPlanarGaussianSupremum

open MeasureTheory ProbabilityTheory Matrix

namespace SRWTightness

/-- The complete bounded planar Gaussian increment supremum input follows by dyadic chaining. -/
theorem planarGaussianIncrementSupInput_internal : PlanarGaussianIncrementSupInput := by
  intro L K hL hK
  let a := Real.sqrt (32 * L * K ^ 2)
  let C := 162 * ∑' n : ℕ, (16 : ℝ) ^ n * Real.exp (-((n : ℝ) + 1) ^ 2 / 2)
  have ha : 0 < a := Real.sqrt_pos.2 (by positivity)
  have hC : 0 ≤ C := mul_nonneg (by norm_num) (tsum_nonneg (fun n ↦ by positivity))
  let b := 1 / (32 * a ^ 2)
  have hb : 0 < b := by dsimp [b]; positivity
  refine ⟨C + Real.exp 2 + 1, b, by positivity, hb, ?_⟩
  intro ι _ _ S J o p r hS ho h0 hr hp hvar U hU
  by_cases hlarge : 8 * a ≤ U
  · let u := U / (4 * a)
    have hu : 0 ≤ u := div_nonneg hU (by positivity)
    have he : a * (2 * u + 4) = U / 2 + 4 * a := by
      dsimp [u]
      field_simp
      <;> ring
    have ht : a * (2 * u + 4) ≤ U := by rw [he]; linarith
    have hm : (multivariateGaussian (0 : EuclideanSpace ℝ ι) S).real
        {φ | ∃ x ∈ J, U ≤ |φ x|} ≤
        (multivariateGaussian (0 : EuclideanSpace ℝ ι) S).real
          {φ | ∃ x ∈ J, a * (2 * u + 4) ≤ |φ x|} := by
      refine measureReal_mono ?_ (measure_ne_top _ _)
      rintro φ ⟨x, hx, hh⟩
      exact ⟨x, hx, ht.trans hh⟩
    have hh := planar_gaussian_shifted_sup_tail S hS J o ho h0 p L K r
      hL hK hr hp hvar u hu
    have hex : -u ^ 2 / 2 = -b * U ^ 2 := by
      dsimp [u, b]
      field_simp
      <;> ring
    change _ ≤ C * Real.exp (-u ^ 2 / 2) at hh
    rw [hex] at hh
    exact (hm.trans hh).trans (mul_le_mul_of_nonneg_right (by linarith [Real.exp_pos (2 : ℝ)])
      (Real.exp_nonneg _))
  · have hs : U ^ 2 ≤ 64 * a ^ 2 := by
      have hh := lt_of_not_ge hlarge
      nlinarith [sq_nonneg (8 * a - U)]
    have hbu : b * U ^ 2 ≤ 2 := by
      dsimp [b]
      rw [one_div, ← div_eq_inv_mul]
      apply (div_le_iff₀ (by positivity : 0 < 32 * a ^ 2)).2
      nlinarith
    have he : 1 ≤ Real.exp 2 * Real.exp (-b * U ^ 2) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp_iff.mpr (by linarith)
    exact measureReal_le_one.trans (he.trans
      (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_nonneg _)))

end SRWTightness
