import SRWTightness.ExternalGaussianMills
import SRWTightness.SourceUpperGaussianMillsCost
import SRWTightness.SourceUpperTerminalConvolution

open MeasureTheory ProbabilityTheory Set
namespace SRWTightness

/-- The actual one-dimensional Gaussian tail has the source terminal block scale. -/
theorem source_upper_terminal_gaussian_tail (hMills : GaussianMillsInput)
    (V η B : ℝ) (hV : 0 < V) (hη : 0 < η) (hB : 0 ≤ B) :
    ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ a d h v q δ ε r : ℝ,
      1 ≤ d → 1 ≤ h → η * d ≤ h → η * d ≤ v → v ≤ V * d → v ≤ a →
      a = 2 * (d - h) + q + (3 / 4 : ℝ) * Real.log h + δ →
      v = d - h + ε → -B ≤ δ → ε ≤ B → 0 < r → h = Real.log r →
      (gaussianReal 0 v.toNNReal).real (Ici a) ≤
      C * r ^ 2 * Real.exp (-2 * d) / d *
        Real.exp (-2 * q - κ * (max q 0) ^ 2 / d) := by
  refine ⟨Real.exp (4 * B) * Real.exp ((1 / (2 * V)) * (3 * B) ^ 2) / η,
    1 / (4 * V), by positivity, by positivity, ?_⟩
  intro a d h v q δ ε r hd hh hhD hvD hvU hva ha hv hδ hε hr hlog
  have hd0 : 0 < d := by linarith
  have hh0 : 0 < h := by linarith
  have hv0 : 0 < v := (mul_pos hη hd0).trans_le hvD
  have hshift := source_upper_gaussian_residual_height a v d h q δ ε B ha hv hδ hε hh
  have hlead := source_upper_gaussian_leading_prefactor a v d h q δ ε B ha hv hδ hε hh0
  have hres := source_upper_gaussian_mills_residual V v d (a - 2 * v) q (3 * B)
    hV hv0 hd hvU (by positivity) hshift
  have hp := mul_le_mul hlead hres (Real.exp_nonneg _) (by positivity)
  have hmills := gaussian_mills_variance_threshold hMills v a hv0 hva
  rw [source_upper_gaussian_mills_factor a v hv0] at hmills
  have htotal := hmills.trans
    (mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 1 / Real.sqrt v))
  apply htotal.trans
  have hs := source_upper_gaussian_mills_prefactor h v η d hη hd0 hh hhD hvD
  have hm := mul_le_mul_of_nonneg_left hs
    (by positivity : 0 ≤ Real.exp (4 * B) * Real.exp (-2 * (d - h) - 2 * q) *
      Real.exp ((1 / (2 * V)) * (3 * B) ^ 2) *
        Real.exp (-((1 / (4 * V)) * (max q 0) ^ 2 / d)))
  have he : Real.exp (-2 * q - (1 / (4 * V)) * (max q 0) ^ 2 / d) =
      Real.exp (-2 * q) * Real.exp (-((1 / (4 * V)) * (max q 0) ^ 2 / d)) := by
    rw [sub_eq_add_neg, Real.exp_add]
  rw [hlog, source_upper_gaussian_radius_factor r d q hr] at hm
  rw [he, hlog, source_upper_gaussian_radius_factor r d q hr]
  convert hm using 1 <;> simp only [div_eq_mul_inv, mul_inv_rev] <;> ring

end SRWTightness
