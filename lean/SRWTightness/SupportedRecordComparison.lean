import SRWTightness.OrderedRecordComparison

open MeasureTheory

namespace SRWTightness

/-- Bounds on the support of a finite measure suffice for its integral. -/
theorem integral_bounds_on_support {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X] (μ : Measure X) [IsFiniteMeasure μ]
    (A : Set X) (hA : ∀ᵐ x ∂μ, x ∈ A) (f : X → ℝ) (lo hi : ℝ) (hlo : 0 ≤ lo)
    (hf : ∀ x ∈ A, lo ≤ f x ∧ f x ≤ hi) :
    lo * μ.real Set.univ ≤ ∫ x, f x ∂μ ∧ (∫ x, f x ∂μ) ≤ hi * μ.real Set.univ := by
  have hfi : Integrable f μ := by
    apply Integrable.of_bound (measurable_of_countable f).aestronglyMeasurable hi
    filter_upwards [hA] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hlo.trans (hf x hx).1)]
    exact (hf x hx).2
  have hl := integral_mono_ae (integrable_const lo) hfi
    (hA.mono (fun x hx ↦ (hf x hx).1))
  have hu := integral_mono_ae hfi (integrable_const hi)
    (hA.mono (fun x hx ↦ (hf x hx).2))
  rw [integral_const, smul_eq_mul] at hl hu
  exact ⟨by simpa only [mul_comm] using hl, by simpa only [mul_comm] using hu⟩

/-- Backward comparison using bounds only on admissible parent and child boundary states. -/
theorem supported_ordered_record_weight_comparison {X R : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (U : X → Measure X) (S : X → R → Measure X) (V : X → ℝ) (A B : Set X)
    (hUf : ∀ x, IsFiniteMeasure (U x)) (hSf : ∀ z r, IsFiniteMeasure (S z r))
    (hUs : ∀ x ∈ A, ∀ᵐ z ∂U x, z ∈ B)
    (hSs : ∀ z ∈ B, ∀ r, ∀ᵐ y ∂S z r, y ∈ A)
    (δ : ℝ) (η Q : R → ℝ) (hQ : ∀ r, 0 ≤ Q r)
    (hU : ∀ x ∈ A, Real.exp (-δ) / 2 ≤ (U x).real Set.univ ∧
      (U x).real Set.univ ≤ Real.exp δ / 2)
    (hV : ∀ x ∈ A, Real.exp (-δ) / 2 ≤ V x ∧ V x ≤ Real.exp δ / 2)
    (hS : ∀ z ∈ B, ∀ r, Real.exp (-η r) * Q r ≤ (S z r).real Set.univ ∧
      (S z r).real Set.univ ≤ Real.exp (η r) * Q r) :
    ∀ rs x, x ∈ A →
      Real.exp (-orderedRecordError δ η rs) * orderedReferenceWeight Q rs ≤
        orderedRecordWeight U S V rs x ∧
      orderedRecordWeight U S V rs x ≤
        Real.exp (orderedRecordError δ η rs) * orderedReferenceWeight Q rs := by
  intro rs
  induction rs with
  | nil =>
    intro x hx
    simpa only [orderedRecordError, orderedReferenceWeight, orderedRecordWeight, mul_one_div]
      using hV x hx
  | cons r rs ih =>
    let lo := Real.exp (-orderedRecordError δ η rs) * orderedReferenceWeight Q rs
    let hi := Real.exp (orderedRecordError δ η rs) * orderedReferenceWeight Q rs
    have href := orderedReferenceWeight_nonneg Q hQ rs
    have hlo : 0 ≤ lo := mul_nonneg (Real.exp_nonneg _) href
    have hhi : 0 ≤ hi := mul_nonneg (Real.exp_nonneg _) href
    let g := fun z ↦ ∫ y, orderedRecordWeight U S V rs y ∂S z r
    have hg : ∀ z ∈ B, lo * (Real.exp (-η r) * Q r) ≤ g z ∧
        g z ≤ hi * (Real.exp (η r) * Q r) := by
      intro z hz
      letI := hSf z r
      have hh := integral_bounds_on_support (S z r) A (hSs z hz r) _ lo hi hlo ih
      exact ⟨(mul_le_mul_of_nonneg_left (hS z hz r).1 hlo).trans hh.1,
        hh.2.trans (mul_le_mul_of_nonneg_left (hS z hz r).2 hhi)⟩
    intro x hx
    letI := hUf x
    have hh := integral_bounds_on_support (U x) B (hUs x hx) g
      (lo * (Real.exp (-η r) * Q r)) (hi * (Real.exp (η r) * Q r))
      (mul_nonneg hlo (mul_nonneg (Real.exp_nonneg _) (hQ r))) hg
    have hl := (mul_le_mul_of_nonneg_left (hU x hx).1
      (mul_nonneg hlo (mul_nonneg (Real.exp_nonneg _) (hQ r)))).trans hh.1
    have hu := hh.2.trans (mul_le_mul_of_nonneg_left (hU x hx).2
      (mul_nonneg hhi (mul_nonneg (Real.exp_nonneg _) (hQ r))))
    constructor
    · calc
        _ = (lo * (Real.exp (-η r) * Q r)) * (Real.exp (-δ) / 2) := by
          simp only [orderedRecordError, orderedReferenceWeight, neg_add, Real.exp_add, lo]
          ring
        _ ≤ _ := hl
    · calc
        _ ≤ (hi * (Real.exp (η r) * Q r)) * (Real.exp δ / 2) := hu
        _ = _ := by
          simp only [orderedRecordError, orderedReferenceWeight, Real.exp_add, hi]
          ring

end SRWTightness
