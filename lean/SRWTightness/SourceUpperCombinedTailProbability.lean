import SRWTightness.ExternalPositiveConvolution
import SRWTightness.SourceUpperResidualMoment

open MeasureTheory Set
namespace SRWTightness

/-- The actual independent sum of a fine-field variable and a nonnegative residual has the
source tail, with constants uniform in the scale and the height. -/
theorem source_upper_combined_tail_probability (hConv : PositiveConvolutionInput)
    (hMoment : SubGaussianPositiveMomentInput) (A b D : ℝ)
    (hA : 0 < A) (hb : 0 < b) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 < C ∧ ∀ (μ ν : Measure ℝ)
      [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      (∀ᵐ u ∂ν, 0 ≤ u) →
      (∀ u : ℝ, 0 ≤ u → ν.real (Ici u) ≤ A * Real.exp (-b * u ^ 2)) →
      ∀ h c : ℝ, 0 < h → 0 ≤ c → c / h ≤ b / 2 →
      (∀ w : ℝ, 0 ≤ w →
        μ.real (Ici w) ≤ D * (1 + w) * Real.exp (-2 * w - c * w ^ 2 / h)) →
      ∀ z : ℝ, 0 ≤ z → (μ.prod ν).real {p | z ≤ p.1 + p.2} ≤
        C * (1 + z) * Real.exp (-2 * z - c * z ^ 2 / (2 * h)) := by
  obtain ⟨M, hM, hm⟩ := source_upper_shifted_fine_tail_bound hMoment A b hA hb
  refine ⟨A * Real.exp (2 / b) + D * M, by positivity, ?_⟩
  intro μ ν _ _ hν hTail h c hh hc hch hFine z hz
  obtain ⟨hi, hp⟩ := hConv μ ν hν z hz
  have hiBound : (∫ u in Icc 0 z, μ.real (Ici (z - u)) ∂ν) ≤
      D * ∫ u in Icc 0 z, (1 + (z - u)) *
        Real.exp (-2 * (z - u) - c * (z - u) ^ 2 / h) ∂ν := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on hi
      (show Continuous (fun u : ℝ ↦ D * ((1 + (z - u)) *
        Real.exp (-2 * (z - u) - c * (z - u) ^ 2 / h))) by
          fun_prop).continuousOn.integrableOn_Icc measurableSet_Icc
    intro u hu
    simpa only [mul_assoc] using hFine (z - u) (sub_nonneg.mpr hu.2)
  have hiFinal := hiBound.trans
    (mul_le_mul_of_nonneg_left (hm ν hTail z h c hz hh hc hch) hD)
  have hratio : (c / 2) / h ≤ b / 2 := by
    calc
      _ = (c / h) / 2 := by ring
      _ ≤ (b / 2) / 2 := div_le_div_of_nonneg_right hch (by norm_num)
      _ ≤ b / 2 := by linarith
  have hr := mul_le_mul_of_nonneg_left
    (source_upper_gaussian_residual_envelope z b (c / 2) h hz hb hh hratio) hA.le
  have he : -2 * z - (c / 2) * z ^ 2 / h = -2 * z - c * z ^ 2 / (2 * h) := by
    ring
  rw [he] at hr
  have hsum := add_le_add ((hTail z hz).trans hr) hiFinal
  exact hp.trans (by convert hsum using 1 <;> ring)

end SRWTightness
