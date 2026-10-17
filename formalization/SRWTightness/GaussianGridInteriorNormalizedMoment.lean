import SRWTightness.GaussianGridFirstNormalizedMoment

open MeasureTheory

namespace SRWTightness

/-- Path increment moments control each normalized interior coordinate difference. -/
theorem gaussianGrid_interior_normalized_moment (T : ℕ → ℝ) (n : ℕ) (hT : T 0 = 0)
    (hgap : ∀ j < n + 1, 1 ≤ T (j + 1) - T j)
    (μ : Measure ((Fin ((n + 1) + 1) → ℝ) × (ℕ → GaussianCoefficientSpace)))
    (C : ℝ) (hC : 0 ≤ C)
    (hm : ∀ r s : ℝ, 0 ≤ r → r ≤ s → s ≤ T (n + 1) →
      Integrable (fun p ↦ (gaussianGridPath T (n + 1) p s -
        gaussianGridPath T (n + 1) p r) ^ 2) μ ∧
      (∫ p, (gaussianGridPath T (n + 1) p s -
        gaussianGridPath T (n + 1) p r) ^ 2 ∂μ) ≤ C * (s - r)) (i : Fin n) :
    Integrable (fun p ↦ ((p.1 i.succ.castSucc - p.1 i.castSucc.castSucc) /
      (T (i.val + 2) - T (i.val + 1))) ^ 2) μ ∧
      (∫ p, ((p.1 i.succ.castSucc - p.1 i.castSucc.castSucc) /
        (T (i.val + 2) - T (i.val + 1))) ^ 2 ∂μ) ≤ C := by
  have hg : ∀ j < n + 1, T j < T (j + 1) := fun j hj ↦ by linarith [hgap j hj]
  have hr : 0 ≤ T (i.val + 1) := by
    simpa only [hT] using timeGridTime_mono T (n + 1) hg
      (show 0 ≤ i.val + 1 by omega) (by omega)
  have hrs : T (i.val + 1) ≤ T (i.val + 2) :=
    timeGridTime_mono T (n + 1) hg (by omega) (by omega)
  have hs : T (i.val + 2) ≤ T (n + 1) :=
    timeGridTime_mono T (n + 1) hg (by omega) (by omega)
  have hh := hm (T (i.val + 1)) (T (i.val + 2)) hr hrs hs
  have he (p : (Fin ((n + 1) + 1) → ℝ) × (ℕ → GaussianCoefficientSpace)) :
      gaussianGridPath T (n + 1) p (T (i.val + 2)) -
        gaussianGridPath T (n + 1) p (T (i.val + 1)) =
        p.1 i.succ.castSucc - p.1 i.castSucc.castSucc := by
    simpa only [Fin.val_succ, Fin.val_castSucc, Nat.add_assoc] using
      (gaussianGrid_coordinate_difference T (n + 1) hg p i.castSucc i.succ).symm
  simp_rw [he] at hh
  exact normalized_increment_moment μ
    (fun p ↦ p.1 i.succ.castSucc - p.1 i.castSucc.castSucc)
    (T (i.val + 2) - T (i.val + 1)) C
    (hgap (i.val + 1) (by omega)) hC hh.1 hh.2

end SRWTightness
