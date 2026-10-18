import SRWTightness.SupportedRecordComparison

open MeasureTheory
namespace SRWTightness

/-- A geometric number of returns, followed by the final escape, with ordered reference records. -/
noncomputable def geometricOrderedReferenceWeight {R : Type*} (p : ℝ) (Q : R → ℝ) : List R → ℝ
  | [] => p
  | r :: rs => (1 - p) * Q r * geometricOrderedReferenceWeight p Q rs

theorem geometricOrderedReferenceWeight_nonneg {R : Type*} (p : ℝ) (hp : 0 ≤ p)
    (hp1 : p ≤ 1) (Q : R → ℝ) (hQ : ∀ r, 0 ≤ Q r) (rs : List R) :
    0 ≤ geometricOrderedReferenceWeight p Q rs := by
  induction rs with
  | nil => exact hp
  | cons r rs ih => exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hp1) (hQ r)) ih

/-- The exact noncritical geometric weight retains the common escape parameter. -/
theorem geometricOrderedReferenceWeight_product {R : Type*} (p : ℝ) (Q : R → ℝ)
    (rs : List R) : geometricOrderedReferenceWeight p Q rs =
      p * (1 - p) ^ rs.length * (rs.map Q).prod := by
  induction rs with
  | nil => simp [geometricOrderedReferenceWeight]
  | cons r rs ih =>
    simp only [geometricOrderedReferenceWeight, List.length_cons, List.map_cons,
      List.prod_cons, ih, pow_succ]
    ring

/-- Backward comparison with arbitrary geometric escape parameter, retaining all joint record-exit kernels. -/
theorem supported_geometric_record_weight_comparison {X R : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (U : X → Measure X) (S : X → R → Measure X) (V : X → ℝ) (A B : Set X)
    (hUf : ∀ x, IsFiniteMeasure (U x)) (hSf : ∀ z r, IsFiniteMeasure (S z r))
    (hUs : ∀ x ∈ A, ∀ᵐ z ∂U x, z ∈ B)
    (hSs : ∀ z ∈ B, ∀ r, ∀ᵐ y ∂S z r, y ∈ A)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (δ : ℝ) (η Q : R → ℝ) (hQ : ∀ r, 0 ≤ Q r)
    (hU : ∀ x ∈ A, Real.exp (-δ) * (1 - p) ≤ (U x).real Set.univ ∧
      (U x).real Set.univ ≤ Real.exp δ * (1 - p))
    (hV : ∀ x ∈ A, Real.exp (-δ) * p ≤ V x ∧ V x ≤ Real.exp δ * p)
    (hS : ∀ z ∈ B, ∀ r, Real.exp (-η r) * Q r ≤ (S z r).real Set.univ ∧
      (S z r).real Set.univ ≤ Real.exp (η r) * Q r) :
    ∀ rs x, x ∈ A →
      Real.exp (-orderedRecordError δ η rs) * geometricOrderedReferenceWeight p Q rs ≤
        orderedRecordWeight U S V rs x ∧
      orderedRecordWeight U S V rs x ≤
        Real.exp (orderedRecordError δ η rs) * geometricOrderedReferenceWeight p Q rs := by
  intro rs
  induction rs with
  | nil =>
    intro x hx
    simpa only [orderedRecordError, geometricOrderedReferenceWeight, orderedRecordWeight, mul_one_div]
      using hV x hx
  | cons r rs ih =>
    let lo := Real.exp (-orderedRecordError δ η rs) * geometricOrderedReferenceWeight p Q rs
    let hi := Real.exp (orderedRecordError δ η rs) * geometricOrderedReferenceWeight p Q rs
    have href := geometricOrderedReferenceWeight_nonneg p hp hp1 Q hQ rs
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
        _ = (lo * (Real.exp (-η r) * Q r)) * (Real.exp (-δ) * (1 - p)) := by
          simp only [orderedRecordError, geometricOrderedReferenceWeight, neg_add, Real.exp_add, lo]
          ring
        _ ≤ _ := hl
    · calc
        _ ≤ (hi * (Real.exp (η r) * Q r)) * (Real.exp δ * (1 - p)) := hu
        _ = _ := by
          simp only [orderedRecordError, geometricOrderedReferenceWeight, Real.exp_add, hi]
          ring

end SRWTightness
