import SRWTightness.SecondMomentSupportProbability

open MeasureTheory

namespace SRWTightness

/-- A nonnegative integrable variable with positive mean has positive second moment. -/
theorem second_moment_pos_of_mean_pos {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : Integrable f μ) (hf₂ : Integrable (fun ω ↦ f ω ^ 2) μ)
    (hf0 : ∀ ω, 0 ≤ f ω) (hm : 0 < ∫ ω, f ω ∂μ) :
    0 < ∫ ω, f ω ^ 2 ∂μ := by
  by_contra hs
  have hs0 := le_of_not_gt hs
  have hm2 : 0 < (∫ ω, f ω ∂μ) ^ 2 := pow_pos hm 2
  have hC : 0 < (∫ ω, f ω ∂μ) ^ 2 / 2 := by positivity
  have hp := second_moment_positive_probability μ f hf hf₂ hf0
    (∫ ω, f ω ∂μ) ((∫ ω, f ω ∂μ) ^ 2 / 2) hm hC le_rfl
    (hs0.trans hC.le)
  have hle := (div_le_iff₀ hC).mp (hp.trans measureReal_le_one)
  nlinarith

/-- The literal squared-mean over second-moment ratio bounds the positive-event probability. -/
theorem second_moment_ratio_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : Integrable f μ) (hf₂ : Integrable (fun ω ↦ f ω ^ 2) μ)
    (hf0 : ∀ ω, 0 ≤ f ω) (hm : 0 < ∫ ω, f ω ∂μ) :
    (∫ ω, f ω ∂μ) ^ 2 / (∫ ω, f ω ^ 2 ∂μ) ≤ μ.real {ω | 0 < f ω} := by
  exact second_moment_positive_probability μ f hf hf₂ hf0 _ _ hm
    (second_moment_pos_of_mean_pos μ f hf hf₂ hf0 hm) le_rfl le_rfl

/-- Uniform moment bounds give the source's positive constant below the literal ratio. -/
theorem second_moment_ratio_lower_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : Integrable f μ) (hf₂ : Integrable (fun ω ↦ f ω ^ 2) μ)
    (hf0 : ∀ ω, 0 ≤ f ω) (c D : ℝ) (hc : 0 < c) (hD : 0 < D)
    (hmean : c ≤ ∫ ω, f ω ∂μ) (hsecond : (∫ ω, f ω ^ 2 ∂μ) ≤ D) :
    c ^ 2 / D ≤ (∫ ω, f ω ∂μ) ^ 2 / (∫ ω, f ω ^ 2 ∂μ) := by
  have hm := hc.trans_le hmean
  have hs := second_moment_pos_of_mean_pos μ f hf hf₂ hf0 hm
  apply (div_le_div_iff₀ hD hs).mpr
  have hsq : c ^ 2 ≤ (∫ ω, f ω ∂μ) ^ 2 := by nlinarith
  exact (mul_le_mul_of_nonneg_left hsecond (sq_nonneg c)).trans
    (mul_le_mul_of_nonneg_right hsq hD.le)

end SRWTightness
