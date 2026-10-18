import SRWTightness.GaussianGridFinalNormalizedMoment
import SRWTightness.IncrementCovarianceWeightedMoment

open MeasureTheory Matrix

namespace SRWTightness

/-- Actual grid path and final increment moments control the weighted inverse Brownian covariance energy. -/
theorem gaussianGrid_inverse_weighted_moment (T : ℕ → ℝ) (n : ℕ) (hT : T 0 = 0)
    (hgap : ∀ j < (n + 1) + 1, 1 ≤ T (j + 1) - T j)
    (μ : Measure ((Fin ((n + 1) + 1) → ℝ) × (ℕ → GaussianCoefficientSpace)))
    (C B : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hm : ∀ r s : ℝ, 0 ≤ r → r ≤ s → s ≤ T (n + 1) →
      Integrable (fun p ↦ (gaussianGridPath T (n + 1) p s -
        gaussianGridPath T (n + 1) p r) ^ 2) μ ∧
      (∫ p, (gaussianGridPath T (n + 1) p s -
        gaussianGridPath T (n + 1) p r) ^ 2 ∂μ) ≤ C * (s - r))
    (hfinal : Integrable (fun p ↦ gaussianGridFinalIncrement T (n + 1) p ^ 2) μ ∧
      (∫ p, gaussianGridFinalIncrement T (n + 1) p ^ 2 ∂μ) ≤ B)
    (e : Fin ((n + 1) + 1) → ℝ) (he : ∀ i, 0 ≤ e i) :
    let K := brownianTimeMatrix T ((n + 1) + 1)
    Integrable (fun p ↦ ∑ i, e i * (K⁻¹ *ᵥ p.1) i ^ 2) μ ∧
      (∫ p, ∑ i, e i * (K⁻¹ *ᵥ p.1) i ^ 2 ∂μ) ≤
        (4 * max C B) * ∑ i, e i := by
  dsimp only
  rw [brownianTimeMatrix_eq_increment T hT _ (fun j hj ↦ by linarith [hgap j hj])]
  have hg : ∀ j < n + 1, 1 ≤ T (j + 1) - T j := fun j hj ↦ hgap j (by omega)
  have hfirst := gaussianGrid_first_normalized_moment T n hT hg μ C hC hm
  have hlast := gaussianGrid_final_normalized_moment T n hgap μ B hB hfinal
  apply incrementCovariance_inverse_weighted_moment μ (n + 1)
    (fun i ↦ T (i.val + 1) - T i.val) (fun i ↦ hgap i.val i.isLt)
    (fun p ↦ p.1) (fun i ↦ (measurable_pi_apply i).comp measurable_fst)
    (max C B) (hC.trans (le_max_left _ _))
    ⟨hfirst.1, hfirst.2.trans (le_max_left _ _)⟩ _ e he
  intro i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · have hh := And.intro hlast.1 (hlast.2.trans (le_max_right C B))
    simpa only [Fin.val_last, Fin.val_succ, Fin.succ_last, Nat.add_assoc] using hh
  · have hh := gaussianGrid_interior_normalized_moment T n hT hg μ C hC hm j
    simpa only [Fin.val_succ, Fin.val_castSucc, Fin.castSucc_succ, Nat.add_assoc] using
      ⟨hh.1, hh.2.trans (le_max_left C B)⟩

end SRWTightness
