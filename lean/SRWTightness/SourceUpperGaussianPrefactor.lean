import SRWTightness.SourceUpperGaussianSquares
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace SRWTightness

/-- The logarithmic centering supplies exactly the inverse h^(3/2) factor. -/
theorem source_upper_gaussian_log_prefactor (h : ℝ) (hh : 0 < h) :
    Real.exp (-((3 : ℝ) / 2) * Real.log h) = (h * Real.sqrt h)⁻¹ := by
  have he : -((3 : ℝ) / 2) * Real.log h = -(Real.log h + Real.log (Real.sqrt h)) := by
    rw [Real.log_sqrt hh.le]
    ring
  rw [he, Real.exp_neg, Real.exp_add, Real.exp_log hh,
    Real.exp_log (Real.sqrt_pos.2 hh)]

/-- Bounded variance and centering errors change the leading exponential by a constant. -/
theorem source_upper_gaussian_leading_prefactor (a v d h q δ ε B : ℝ)
    (ha : a = 2 * (d - h) + q + (3 / 4 : ℝ) * Real.log h + δ)
    (hv : v = d - h + ε) (hδ : -B ≤ δ) (hε : ε ≤ B) (hh : 0 < h) :
    Real.exp (-2 * a + 2 * v) ≤
      Real.exp (4 * B) * Real.exp (-2 * (d - h) - 2 * q) / (h * Real.sqrt h) := by
  have he : -2 * a + 2 * v ≤
      4 * B + (-2 * (d - h) - 2 * q) + (-((3 : ℝ) / 2) * Real.log h) := by
    rw [ha, hv]
    linarith only [hδ, hε]
  calc
    Real.exp (-2 * a + 2 * v) ≤
        Real.exp (4 * B + (-2 * (d - h) - 2 * q) +
          (-((3 : ℝ) / 2) * Real.log h)) := Real.exp_le_exp.mpr he
    _ = _ := by
      rw [Real.exp_add, Real.exp_add, source_upper_gaussian_log_prefactor h hh,
        div_eq_mul_inv]

/-- The residual height is the source height plus a nonnegative logarithm and bounded error. -/
theorem source_upper_gaussian_residual_height (a v d h q δ ε B : ℝ)
    (ha : a = 2 * (d - h) + q + (3 / 4 : ℝ) * Real.log h + δ)
    (hv : v = d - h + ε) (hδ : -B ≤ δ) (hε : ε ≤ B) (hh : 1 ≤ h) :
    q - 3 * B ≤ a - 2 * v := by
  have hl := Real.log_nonneg hh
  rw [ha, hv]
  linarith only [hδ, hε, hl]

/-- Comparable positive variance scales supply the reciprocal-d terminal prefactor. -/
theorem source_upper_gaussian_reciprocal_scale (h v η d : ℝ)
    (hη : 0 < η) (hd : 0 < d) (hh : η * d ≤ h) (hv : η * d ≤ v) :
    h / Real.sqrt v * Real.exp (-((3 : ℝ) / 2) * Real.log h) ≤ 1 / (η * d) := by
  have hh0 : 0 < h := (mul_pos hη hd).trans_le hh
  have hv0 : 0 < v := (mul_pos hη hd).trans_le hv
  have hs : η * d ≤ Real.sqrt v * Real.sqrt h := by
    have hb := mul_le_mul (Real.sqrt_le_sqrt hv) (Real.sqrt_le_sqrt hh)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    simpa only [Real.mul_self_sqrt (mul_pos hη hd).le] using hb
  rw [source_upper_gaussian_log_prefactor h hh0]
  have he : h / Real.sqrt v * (h * Real.sqrt h)⁻¹ =
      1 / (Real.sqrt v * Real.sqrt h) := by
    field_simp
  rw [he]
  exact one_div_le_one_div_of_le (mul_pos hη hd) hs

end SRWTightness
