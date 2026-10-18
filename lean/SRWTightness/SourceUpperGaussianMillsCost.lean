import SRWTightness.SourceUpperGaussianShift
import SRWTightness.SourceUpperGaussianPrefactor

namespace SRWTightness

/-- The one-dimensional Mills residual keeps uniform height decay at comparable variance. -/
theorem source_upper_gaussian_mills_residual (V v d ζ q E : ℝ)
    (hV : 0 < V) (hv : 0 < v) (hd : 1 ≤ d) (hvD : v ≤ V * d)
    (hE : 0 ≤ E) (hshift : q - E ≤ ζ) :
    Real.exp (-(ζ ^ 2 / (2 * v))) ≤
      Real.exp ((1 / (2 * V)) * E ^ 2) *
        Real.exp (-((1 / (4 * V)) * (max q 0) ^ 2 / d)) := by
  have hcost := div_le_div_of_nonneg_left (sq_nonneg ζ)
    (show 0 < 2 * v by positivity) (mul_le_mul_of_nonneg_left hvD (by norm_num : (0 : ℝ) ≤ 2))
  have he : ζ ^ 2 / (2 * (V * d)) = (1 / (2 * V)) * ζ ^ 2 / d := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he] at hcost
  have hb := (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans
    (source_upper_gaussian_shift_exponential q ζ E (1 / (2 * V)) d hE
      (by positivity) hd hshift)
  have hk : (1 / (2 * V)) / 2 = (1 : ℝ) / (4 * V) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  simpa only [hk] using hb

/-- Removing the extra h factor can only improve the Mills prefactor for h>=1. -/
theorem source_upper_gaussian_mills_prefactor (h v η d : ℝ)
    (hη : 0 < η) (hd : 0 < d) (hh : 1 ≤ h) (hhD : η * d ≤ h)
    (hvD : η * d ≤ v) :
    (1 / Real.sqrt v) * (h * Real.sqrt h)⁻¹ ≤ 1 / (η * d) := by
  have hv : 0 < v := (mul_pos hη hd).trans_le hvD
  have hh0 : 0 < h := by linarith
  have hb := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hh (Real.sqrt_nonneg v))
    (by positivity : 0 ≤ (h * Real.sqrt h)⁻¹)
  have hs := source_upper_gaussian_reciprocal_scale h v η d hη hd hhD hvD
  rw [source_upper_gaussian_log_prefactor h hh0] at hs
  exact hb.trans hs

/-- Exact square completion in the Mills exponential. -/
theorem source_upper_gaussian_mills_factor (a v : ℝ) (hv : 0 < v) :
    Real.exp (-a ^ 2 / (2 * v)) =
      Real.exp (-2 * a + 2 * v) * Real.exp (-((a - 2 * v) ^ 2 / (2 * v))) := by
  have he := source_upper_gaussian_linear_square a 0 v hv
  simp only [sub_zero, mul_zero] at he
  rw [he, sub_eq_add_neg, Real.exp_add]

end SRWTightness
