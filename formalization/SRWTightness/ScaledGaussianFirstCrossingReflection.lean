import SRWTightness.ScaledGaussianReflectionEvent

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Reflection at a fixed candidate first crossing retains all earlier grid inequalities. -/
theorem scaled_gaussian_first_crossing_reflection (T r t q b : ℝ) (hT : 0 < T)
    (hr : 0 ≤ r) (hrt : r ≤ t) (ht : t ≤ T) (k : ℕ)
    (τ : Fin k → Set.Icc (0 : ℝ) r) :
    gaussianCoefficientLaw.real {ω |
      (q ≤ Real.sqrt T * gaussianDyadicPath ω (r / T) ∧
        ∀ j, Real.sqrt T * gaussianDyadicPath ω ((τ j : ℝ) / T) < q) ∧
      Real.sqrt T * gaussianDyadicPath ω (t / T) ≤ b} =
    gaussianCoefficientLaw.real {ω |
      (q ≤ Real.sqrt T * gaussianDyadicPath ω (r / T) ∧
        ∀ j, Real.sqrt T * gaussianDyadicPath ω ((τ j : ℝ) / T) < q) ∧
      2 * (Real.sqrt T * gaussianDyadicPath ω (r / T)) -
        Real.sqrt T * gaussianDyadicPath ω (t / T) ≤ b} := by
  let A : Set (Set.Icc (0 : ℝ) r → ℝ) :=
    {p | q ≤ p ⟨r, hr, le_rfl⟩ ∧ ∀ j, p (τ j) < q}
  have hA : MeasurableSet A := by
    simp only [A, Set.setOf_and, Set.setOf_forall]
    exact (measurableSet_le measurable_const (measurable_pi_apply _)).inter
      (MeasurableSet.iInter (fun j ↦ measurableSet_lt (measurable_pi_apply (τ j))
        measurable_const))
  exact scaled_gaussian_reflection_event T r t hT hr hrt ht A (Set.Iic b)
    hA measurableSet_Iic

end SRWTightness
