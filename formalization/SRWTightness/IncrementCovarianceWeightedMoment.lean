import SRWTightness.IncrementCovarianceInverseMoment
import SRWTightness.WeightedCoordinateMoment

open MeasureTheory Matrix

namespace SRWTightness

/-- The weighted inverse covariance energy has a dimension-independent moment bound. -/
theorem incrementCovariance_inverse_weighted_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (n : ℕ) (d : Fin (n + 1) → ℝ) (hd : ∀ i, 1 ≤ d i)
    (Y : Ω → Fin (n + 1) → ℝ) (hY : ∀ i, Measurable (fun ω ↦ Y ω i))
    (M : ℝ) (hM : 0 ≤ M)
    (hfirst : Integrable (fun ω ↦ (Y ω 0 / d 0) ^ 2) μ ∧
      (∫ ω, (Y ω 0 / d 0) ^ 2 ∂μ) ≤ M)
    (hstep : ∀ i : Fin n,
      Integrable (fun ω ↦ ((Y ω i.succ - Y ω i.castSucc) / d i.succ) ^ 2) μ ∧
      (∫ ω, ((Y ω i.succ - Y ω i.castSucc) / d i.succ) ^ 2 ∂μ) ≤ M)
    (e : Fin (n + 1) → ℝ) (he : ∀ i, 0 ≤ e i) :
    Integrable (fun ω ↦ ∑ i, e i * ((incrementCovariance d)⁻¹ *ᵥ Y ω) i ^ 2) μ ∧
      (∫ ω, ∑ i, e i * ((incrementCovariance d)⁻¹ *ᵥ Y ω) i ^ 2 ∂μ) ≤
        (4 * M) * ∑ i, e i := by
  have hh := incrementCovariance_inverse_moment μ n d hd Y hY M hM hfirst hstep
  exact weighted_coordinate_moment μ (fun ω ↦ (incrementCovariance d)⁻¹ *ᵥ Y ω)
    e he (4 * M) (fun i ↦ (hh i).1) (fun i ↦ (hh i).2)

end SRWTightness
