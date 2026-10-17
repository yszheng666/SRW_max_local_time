import SRWTightness.GaussianResidualRectangle
import SRWTightness.ProductEventRealBounds

open MeasureTheory ProbabilityTheory Matrix

namespace SRWTightness

/-- Integrating the independent residual unit rectangle preserves the base-event probability. -/
theorem gaussian_residual_window_product {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : Matrix (Fin 2) (Fin 2) ℝ) (hR : R.PosDef) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x, (gaussianCovarianceDensity R x).toReal ≤ C)
    (s : Set Ω) (hs : MeasurableSet s) (a : Ω → Fin 2 → ℝ) (ha : Measurable a) :
    (μ.prod (gaussianCoordinateLaw R)).real
      {p | p.1 ∈ s ∧ ∀ j, a p.1 j ≤ p.2 j ∧ p.2 j < a p.1 j + 1} ≤ C * μ.real s := by
  letI := gaussianCoordinateLaw_isProbabilityMeasure R
  let E : Set (Ω × (Fin 2 → ℝ)) :=
    {p | p.1 ∈ s ∧ ∀ j, a p.1 j ≤ p.2 j ∧ p.2 j < a p.1 j + 1}
  have hE : MeasurableSet E := by
    simp only [E, Set.setOf_and, Set.setOf_forall]
    apply (hs.preimage measurable_fst).inter
    exact MeasurableSet.iInter fun j ↦
      (measurableSet_le (by fun_prop) (by fun_prop)).inter
        (measurableSet_lt (by fun_prop) (by fun_prop))
  exact (product_event_real_bounds μ (gaussianCoordinateLaw R) s E 0 C
    le_rfl hC hs hE (fun _ hp ↦ ⟨hp.1, Set.mem_univ _⟩) (by
      intro x hx
      constructor
      · exact measureReal_nonneg
      · have he : Prod.mk x ⁻¹' E =
            Set.pi Set.univ (fun j ↦ Set.Ico (a x j) (a x j + 1)) := by
          ext r
          simp [E, hx, Set.mem_pi]
        rw [he]
        exact gaussian_unit_rectangle_bound R hR C hC hbound (a x))).2

end SRWTightness
