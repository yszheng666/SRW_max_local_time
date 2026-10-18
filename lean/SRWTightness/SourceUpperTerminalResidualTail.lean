import SRWTightness.SourceUpperResidualAbsorption
import SRWTightness.SourceUpperGaussianMillsCost
import SRWTightness.SourceUpperTerminalConvolution

namespace SRWTightness

/-- The residual-field tail envelope has the same terminal-block scale as the Gaussian terms. -/
theorem source_upper_terminal_residual_tail (c H η B : ℝ)
    (hc : 0 < c) (hH : 0 < H) (hη : 0 < η) (hB : 0 ≤ B) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ a d h v q δ ε r : ℝ,
      1 ≤ d → 1 ≤ h → η * d ≤ h → η * d ≤ v → h ≤ H * d →
      a = 2 * (d - h) + q + (3 / 4 : ℝ) * Real.log h + δ →
      v = d - h + ε → -B ≤ δ → ε ≤ B → 0 < r → h = Real.log r →
      (1 + a) * Real.exp (-2 * a - c * a ^ 2 / h) ≤
      C * r ^ 2 * Real.exp (-2 * d) / d *
        Real.exp (-2 * q - κ * (max q 0) ^ 2 / d) := by
  let K := 2 + 2 / c
  let V := H / c
  have hK : 0 < K := by dsimp [K]; positivity
  have hV : 0 < V := by dsimp [V]; positivity
  refine ⟨K * Real.exp (4 * B) * Real.exp ((1 / (2 * V)) * (3 * B) ^ 2) / η,
    1 / (4 * V), by positivity, by positivity, ?_⟩
  intro a d h v q δ ε r hd hh hhD hvD hhU ha hv hδ hε hr hlog
  have hd0 : 0 < d := by linarith
  have hh0 : 0 < h := by linarith
  have hv0 : 0 < v := (mul_pos hη hd0).trans_le hvD
  have hshift := source_upper_gaussian_residual_height a v d h q δ ε B ha hv hδ hε hh
  have hvar : h / c ≤ V * d := by
    have hb := div_le_div_of_nonneg_right hhU hc.le
    calc
      h / c ≤ (H * d) / c := hb
      _ = V * d := by dsimp [V]; ring
  have hres := source_upper_gaussian_mills_residual V (h / c) d a q (3 * B)
    hV (by positivity) hd hvar (by positivity) (by linarith only [hshift, hv0])
  have heq : a ^ 2 / (2 * (h / c)) = c * a ^ 2 / (2 * h) := by
    field_simp
  rw [heq] at hres
  have hpoly := source_upper_residual_polynomial c h a hc hh
  have hsmall := source_upper_residual_variance v hv0
  have hlead := source_upper_gaussian_leading_prefactor a v d h q δ ε B ha hv hδ hε hh0
  have hp := mul_le_mul hpoly hsmall (Real.exp_nonneg _) (by positivity)
  have hp2 := mul_le_mul hp hlead (Real.exp_nonneg _) (by positivity)
  have hp3 := mul_le_mul hp2 hres (Real.exp_nonneg _) (by positivity)
  have hfactor : (1 + a) * Real.exp (-2 * a - c * a ^ 2 / h) =
      (((1 + a) * Real.exp (-(c * a ^ 2 / (2 * h))) * Real.exp (-2 * v)) *
        Real.exp (-2 * a + 2 * v)) * Real.exp (-(c * a ^ 2 / (2 * h))) := by
    simp only [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [← hfactor] at hp3
  apply hp3.trans
  have hs := source_upper_gaussian_reciprocal_scale h v η d hη hd0 hhD hvD
  rw [source_upper_gaussian_log_prefactor h hh0] at hs
  have hm := mul_le_mul_of_nonneg_left hs
    (by positivity : 0 ≤ K * Real.exp (4 * B) * Real.exp (-2 * (d - h) - 2 * q) *
      Real.exp ((1 / (2 * V)) * (3 * B) ^ 2) *
        Real.exp (-((1 / (4 * V)) * (max q 0) ^ 2 / d)))
  have he : Real.exp (-2 * q - (1 / (4 * V)) * (max q 0) ^ 2 / d) =
      Real.exp (-2 * q) * Real.exp (-((1 / (4 * V)) * (max q 0) ^ 2 / d)) := by
    rw [sub_eq_add_neg, Real.exp_add]
  rw [hlog, source_upper_gaussian_radius_factor r d q hr] at hm
  rw [he, hlog, source_upper_gaussian_radius_factor r d q hr]
  dsimp [K] at hm
  convert hm using 1 <;> simp only [div_eq_mul_inv, mul_inv_rev] <;> ring

end SRWTightness
