import SRWTightness.SupportedRecordComparison

open MeasureTheory
namespace SRWTightness

/-- Upper record bounds need no positive lower comparison for the child marginals. -/
theorem supported_ordered_record_weight_upper {X R : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (U : X → Measure X) (S : X → R → Measure X) (V : X → ℝ) (A B : Set X)
    (hUf : ∀ x, IsFiniteMeasure (U x)) (hSf : ∀ z r, IsFiniteMeasure (S z r))
    (hUs : ∀ x ∈ A, ∀ᵐ z ∂U x, z ∈ B)
    (hSs : ∀ z ∈ B, ∀ r, ∀ᵐ y ∂S z r, y ∈ A)
    (δ : ℝ) (η Q : R → ℝ) (hQ : ∀ r, 0 ≤ Q r)
    (hU : ∀ x ∈ A, (U x).real Set.univ ≤ Real.exp δ / 2)
    (hV : ∀ x ∈ A, 0 ≤ V x ∧ V x ≤ Real.exp δ / 2)
    (hS : ∀ z ∈ B, ∀ r, (S z r).real Set.univ ≤ Real.exp (η r) * Q r) :
    ∀ rs x, x ∈ A →
      0 ≤ orderedRecordWeight U S V rs x ∧
      orderedRecordWeight U S V rs x ≤
        Real.exp (orderedRecordError δ η rs) * orderedReferenceWeight Q rs := by
  intro rs
  induction rs with
  | nil =>
    intro x hx
    simpa only [orderedRecordError, orderedReferenceWeight, orderedRecordWeight, mul_one_div]
      using hV x hx
  | cons r rs ih =>
    let hi := Real.exp (orderedRecordError δ η rs) * orderedReferenceWeight Q rs
    have hhi : 0 ≤ hi :=
      mul_nonneg (Real.exp_nonneg _) (orderedReferenceWeight_nonneg Q hQ rs)
    let g := fun z ↦ ∫ y, orderedRecordWeight U S V rs y ∂S z r
    have hg : ∀ z ∈ B, 0 ≤ g z ∧ g z ≤ hi * (Real.exp (η r) * Q r) := by
      intro z hz
      letI := hSf z r
      have hh := integral_bounds_on_support (S z r) A (hSs z hz r) _ 0 hi le_rfl ih
      refine ⟨by simpa only [zero_mul, orderedRecordWeight, g] using hh.1, ?_⟩
      exact hh.2.trans (mul_le_mul_of_nonneg_left (hS z hz r) hhi)
    intro x hx
    letI := hUf x
    have hh := integral_bounds_on_support (U x) B (hUs x hx) g
      0 (hi * (Real.exp (η r) * Q r)) le_rfl hg
    have hu := hh.2.trans (mul_le_mul_of_nonneg_left (hU x hx)
      (mul_nonneg hhi (mul_nonneg (Real.exp_nonneg _) (hQ r))))
    refine ⟨by simpa only [zero_mul, orderedRecordWeight, g] using hh.1, ?_⟩
    calc
      _ ≤ (hi * (Real.exp (η r) * Q r)) * (Real.exp δ / 2) := hu
      _ = _ := by
        simp only [orderedRecordError, orderedReferenceWeight, Real.exp_add, hi]
        ring

end SRWTightness
