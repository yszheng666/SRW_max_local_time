import SRWTightness.SourceUpperGaussianShift
import SRWTightness.SourceUpperGaussianPrefactor

open MeasureTheory Set
namespace SRWTightness

/-- Keep the actual h prefactor while absorbing bounded shifts of the source height. -/
theorem source_upper_gaussian_shifted_convolution_h
    (hIntegral : WeightedGaussianIntegralInput) (c H V E : ℝ)
    (hc : 0 < c) (hH : 0 < H) (hV : 0 < V) (hE : 0 ≤ E) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ a d h v q ζ : ℝ,
      1 ≤ d → 1 ≤ h → 0 < v → h ≤ H * d → v ≤ V * d → q - E ≤ ζ →
      (∫ z in Icc 0 a, (1 + z) *
        Real.exp (-((ζ - z) ^ 2 / (2 * v) + c * z ^ 2 / h))) ≤
      C * h * Real.exp (-(κ * (max q 0) ^ 2 / d)) := by
  obtain ⟨C, hC, hbound⟩ := source_upper_gaussian_convolution_bound hIntegral c hc
  let κ := c / (2 * (H + c * V))
  have hκ : 0 < κ := by dsimp [κ]; positivity
  refine ⟨C * Real.exp (κ * E ^ 2), κ / 2, by positivity, by positivity, ?_⟩
  intro a d h v q ζ hd hh hv hhD hvD hshift
  have hcost := source_upper_gaussian_scaled_cost c H V d h v |ζ| |ζ| hc hH hV
    (by linarith) (by linarith) hv hhD hvD (abs_nonneg _) le_rfl
  simp only [sq_abs] at hcost
  have he := (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans
    (source_upper_gaussian_shift_exponential q ζ E κ d hE hκ hd hshift)
  have hm := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ C * h)
  exact (hbound a ζ v h hv hh).trans (by convert hm using 1 <;> ring)

/-- The source logarithmic radius converts the leading cost to the block-area factor. -/
theorem source_upper_gaussian_radius_factor (r d q : ℝ) (hr : 0 < r) :
    Real.exp (-2 * (d - Real.log r) - 2 * q) =
      r ^ 2 * Real.exp (-2 * d) * Real.exp (-2 * q) := by
  have he : -2 * (d - Real.log r) - 2 * q =
      (Real.log r + Real.log r) + (-2 * d) + (-2 * q) := by ring
  rw [he, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hr]
  ring

/-- Complete analytic convolution term in the source terminal-block estimate. -/
theorem source_upper_terminal_convolution
    (hIntegral : WeightedGaussianIntegralInput) (c H V η B : ℝ)
    (hc : 0 < c) (hH : 0 < H) (hV : 0 < V) (hη : 0 < η) (hB : 0 ≤ B) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ a d h v q δ ε r : ℝ,
      1 ≤ d → 1 ≤ h → η * d ≤ h → η * d ≤ v → h ≤ H * d → v ≤ V * d →
      a = 2 * (d - h) + q + (3 / 4 : ℝ) * Real.log h + δ →
      v = d - h + ε → -B ≤ δ → ε ≤ B → 0 < r → h = Real.log r →
      (1 / Real.sqrt v) * (∫ z in Icc 0 a, (1 + z) *
        Real.exp (-(a - z) ^ 2 / (2 * v) - 2 * z - c * z ^ 2 / h)) ≤
      C * r ^ 2 * Real.exp (-2 * d) / d *
        Real.exp (-2 * q - κ * (max q 0) ^ 2 / d) := by
  obtain ⟨C, κ, hC, hκ, hbound⟩ :=
    source_upper_gaussian_shifted_convolution_h hIntegral c H V (3 * B) hc hH hV
      (by positivity)
  refine ⟨C * Real.exp (4 * B) / η, κ, by positivity, hκ, ?_⟩
  intro a d h v q δ ε r hd hh hhL hvL hhU hvU ha hv hδ hε hr hlog
  have hd0 : 0 < d := by linarith
  have hh0 : 0 < h := by linarith
  have hv0 : 0 < v := (mul_pos hη hd0).trans_le hvL
  have hshift := source_upper_gaussian_residual_height a v d h q δ ε B ha hv hδ hε hh
  have hconv := hbound a d h v q (a - 2 * v) hd hh hv0 hhU hvU hshift
  have hlead := source_upper_gaussian_leading_prefactor a v d h q δ ε B ha hv hδ hε hh0
  have h1 := mul_le_mul_of_nonneg_left hconv (Real.exp_nonneg (-2 * a + 2 * v))
  have h2 := mul_le_mul_of_nonneg_right hlead
    (by positivity : 0 ≤ C * h * Real.exp (-(κ * (max q 0) ^ 2 / d)))
  have h3 := mul_le_mul_of_nonneg_left (h1.trans h2)
    (by positivity : 0 ≤ 1 / Real.sqrt v)
  rw [source_upper_gaussian_convolution_factor a v h c hv0]
  apply h3.trans
  have hs := source_upper_gaussian_reciprocal_scale h v η d hη hd0 hhL hvL
  rw [source_upper_gaussian_log_prefactor h hh0] at hs
  have hm := mul_le_mul_of_nonneg_left hs
    (by positivity : 0 ≤ C * Real.exp (4 * B) * Real.exp (-2 * (d - h) - 2 * q) *
      Real.exp (-(κ * (max q 0) ^ 2 / d)))
  have he : Real.exp (-2 * q - κ * (max q 0) ^ 2 / d) =
      Real.exp (-2 * q) * Real.exp (-(κ * (max q 0) ^ 2 / d)) := by
    rw [sub_eq_add_neg, Real.exp_add]
  rw [hlog, source_upper_gaussian_radius_factor r d q hr] at hm
  rw [he, hlog, source_upper_gaussian_radius_factor r d q hr]
  convert hm using 1 <;> simp only [div_eq_mul_inv, mul_inv_rev] <;> ring

end SRWTightness
