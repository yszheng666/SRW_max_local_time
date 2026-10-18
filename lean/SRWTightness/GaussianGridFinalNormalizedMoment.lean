import SRWTightness.GaussianGridInteriorNormalizedMoment

open MeasureTheory

namespace SRWTightness

/-- The normalized final coordinate difference inherits the final increment moment bound. -/
theorem gaussianGrid_final_normalized_moment (T : ℕ → ℝ) (n : ℕ)
    (hgap : ∀ j < (n + 1) + 1, 1 ≤ T (j + 1) - T j)
    (μ : Measure ((Fin ((n + 1) + 1) → ℝ) × (ℕ → GaussianCoefficientSpace)))
    (B : ℝ) (hB : 0 ≤ B)
    (hm : Integrable (fun p ↦ gaussianGridFinalIncrement T (n + 1) p ^ 2) μ ∧
      (∫ p, gaussianGridFinalIncrement T (n + 1) p ^ 2 ∂μ) ≤ B) :
    Integrable (fun p ↦ ((p.1 (Fin.last (n + 1)) - p.1 (Fin.last n).castSucc) /
      (T (n + 2) - T (n + 1))) ^ 2) μ ∧
      (∫ p, ((p.1 (Fin.last (n + 1)) - p.1 (Fin.last n).castSucc) /
        (T (n + 2) - T (n + 1))) ^ 2 ∂μ) ≤ B := by
  have hg : ∀ j < n + 1, T j < T (j + 1) := fun j hj ↦ by linarith [hgap j (by omega)]
  simp_rw [gaussianGrid_coordinate_final_difference T n hg]
  exact normalized_bounded_moment μ (gaussianGridFinalIncrement T (n + 1))
    (T (n + 2) - T (n + 1)) B (hgap (n + 1) (by omega)) hB hm.1 hm.2

end SRWTightness
