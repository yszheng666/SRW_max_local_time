import SRWTightness.GaussianGridCoordinateNodes
import SRWTightness.NormalizedIncrementMoment

open MeasureTheory

namespace SRWTightness

/-- A path increment moment bounds the first normalized observation on the actual grid. -/
theorem gaussianGrid_first_normalized_moment (T : ℕ → ℝ) (n : ℕ) (hT : T 0 = 0)
    (hgap : ∀ j < n + 1, 1 ≤ T (j + 1) - T j)
    (μ : Measure ((Fin ((n + 1) + 1) → ℝ) × (ℕ → GaussianCoefficientSpace)))
    (C : ℝ) (hC : 0 ≤ C)
    (hm : ∀ r s : ℝ, 0 ≤ r → r ≤ s → s ≤ T (n + 1) →
      Integrable (fun p ↦ (gaussianGridPath T (n + 1) p s -
        gaussianGridPath T (n + 1) p r) ^ 2) μ ∧
      (∫ p, (gaussianGridPath T (n + 1) p s -
        gaussianGridPath T (n + 1) p r) ^ 2 ∂μ) ≤ C * (s - r)) :
    Integrable (fun p ↦ (p.1 0 / (T 1 - T 0)) ^ 2) μ ∧
      (∫ p, (p.1 0 / (T 1 - T 0)) ^ 2 ∂μ) ≤ C := by
  have hg : ∀ j < n + 1, T j < T (j + 1) := fun j hj ↦ by linarith [hgap j hj]
  have h01 : 1 ≤ T 1 := by simpa only [hT, sub_zero] using hgap 0 (by omega)
  have htime : T 1 ≤ T (n + 1) := timeGridTime_mono T (n + 1) hg (by omega) (by omega)
  have hh := hm 0 (T 1) (by norm_num) (by linarith) htime
  have he (p : (Fin ((n + 1) + 1) → ℝ) × (ℕ → GaussianCoefficientSpace)) :
      gaussianGridPath T (n + 1) p (T 1) - gaussianGridPath T (n + 1) p 0 = p.1 0 := by
    have hn := gaussianGrid_coordinate_node T (n + 1) hg p (0 : Fin (n + 1))
    simpa only [Fin.val_zero, zero_add, Fin.castSucc_zero,
      gaussianGrid_coordinate_zero T (n + 1) hT hg p, sub_zero] using hn
  simp_rw [he] at hh
  have hh' := normalized_increment_moment μ (fun p ↦ p.1 0) (T 1) C h01 hC hh.1
    (by simpa only [sub_zero] using hh.2)
  simpa only [hT, sub_zero] using hh'

end SRWTightness
