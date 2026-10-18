import SRWTightness.SuffixCoordinateMoment

open MeasureTheory

namespace SRWTightness

/-- A time-linear second moment becomes uniformly bounded after division by a gap at least one. -/
theorem normalized_increment_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (L C : ℝ) (hL : 1 ≤ L) (hC : 0 ≤ C)
    (hi : Integrable (fun ω ↦ X ω ^ 2) μ)
    (hm : (∫ ω, X ω ^ 2 ∂μ) ≤ C * L) :
    Integrable (fun ω ↦ (X ω / L) ^ 2) μ ∧
      (∫ ω, (X ω / L) ^ 2 ∂μ) ≤ C := by
  have hL0 : 0 < L := by linarith
  have he : (fun ω ↦ (X ω / L) ^ 2) = (fun ω ↦ X ω ^ 2 / L ^ 2) := by
    funext ω
    exact div_pow _ _ _
  rw [he]
  refine ⟨hi.div_const _, ?_⟩
  rw [integral_div]
  apply (div_le_iff₀ (sq_pos_of_pos hL0)).mpr
  apply hm.trans
  exact mul_le_mul_of_nonneg_left (by nlinarith : L ≤ L ^ 2) hC

/-- A bounded second moment also survives division by a gap at least one. -/
theorem normalized_bounded_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (L C : ℝ) (hL : 1 ≤ L) (hC : 0 ≤ C)
    (hi : Integrable (fun ω ↦ X ω ^ 2) μ)
    (hm : (∫ ω, X ω ^ 2 ∂μ) ≤ C) :
    Integrable (fun ω ↦ (X ω / L) ^ 2) μ ∧
      (∫ ω, (X ω / L) ^ 2 ∂μ) ≤ C := by
  apply normalized_increment_moment μ X L C hL hC hi
  exact hm.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hL hC)

end SRWTightness
