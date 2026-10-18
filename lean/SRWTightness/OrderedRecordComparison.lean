import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory

namespace SRWTightness

/-- Backward integration of ordered child records, retaining their joint exit-position laws. -/
noncomputable def orderedRecordWeight {X R : Type*} [MeasurableSpace X]
    (U : X → Measure X) (S : X → R → Measure X) (V : X → ℝ) : List R → X → ℝ
  | [], x => V x
  | r :: rs, x => ∫ z, ∫ y, orderedRecordWeight U S V rs y ∂S z r ∂U x

/-- Reference weight for a parent with critical geometric offspring and independent child records. -/
noncomputable def orderedReferenceWeight {R : Type*} (Q : R → ℝ) : List R → ℝ
  | [] => 1 / 2
  | r :: rs => (1 / 2) * Q r * orderedReferenceWeight Q rs

/-- One entrance decision per child and one final exit decision, plus child errors. -/
def orderedRecordError {R : Type*} (δ : ℝ) (η : R → ℝ) : List R → ℝ
  | [] => δ
  | r :: rs => δ + η r + orderedRecordError δ η rs

/-- Nonnegativity of the geometric offspring reference weight. -/
theorem orderedReferenceWeight_nonneg {R : Type*} (Q : R → ℝ) (hQ : ∀ r, 0 ≤ Q r)
    (rs : List R) : 0 ≤ orderedReferenceWeight Q rs := by
  induction rs with
  | nil => norm_num [orderedReferenceWeight]
  | cons r rs ih => exact mul_nonneg (mul_nonneg (by norm_num) (hQ r)) ih

/-- Explicit geometric offspring mass times the ordered child masses. -/
theorem orderedReferenceWeight_product {R : Type*} (Q : R → ℝ) (rs : List R) :
    orderedReferenceWeight Q rs = (1 / 2 : ℝ) ^ (rs.length + 1) * (rs.map Q).prod := by
  induction rs with
  | nil => norm_num [orderedReferenceWeight]
  | cons r rs ih =>
    simp only [orderedReferenceWeight, List.length_cons, List.map_cons, List.prod_cons, ih,
      pow_succ]
    ring

/-- A parent with l children incurs l+1 decision errors and all child errors. -/
theorem orderedRecordError_sum {R : Type*} (δ : ℝ) (η : R → ℝ) (rs : List R) :
    orderedRecordError δ η rs = ((rs.length : ℝ) + 1) * δ + (rs.map η).sum := by
  induction rs with
  | nil => simp [orderedRecordError]
  | cons r rs ih =>
    simp only [orderedRecordError, List.length_cons, List.map_cons, List.sum_cons, ih,
      Nat.cast_add, Nat.cast_one]
    ring

/-- Uniform child marginals suffice for multiplicative comparison; exit independence is unnecessary. -/
theorem ordered_record_weight_comparison {X R : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (U : X → Measure X) (S : X → R → Measure X) (V : X → ℝ)
    (hUf : ∀ x, IsFiniteMeasure (U x)) (hSf : ∀ z r, IsFiniteMeasure (S z r))
    (δ : ℝ) (η Q : R → ℝ) (hQ : ∀ r, 0 ≤ Q r)
    (hU : ∀ x, Real.exp (-δ) / 2 ≤ (U x).real Set.univ ∧
      (U x).real Set.univ ≤ Real.exp δ / 2)
    (hV : ∀ x, Real.exp (-δ) / 2 ≤ V x ∧ V x ≤ Real.exp δ / 2)
    (hS : ∀ z r, Real.exp (-η r) * Q r ≤ (S z r).real Set.univ ∧
      (S z r).real Set.univ ≤ Real.exp (η r) * Q r) :
    ∀ rs x,
      Real.exp (-orderedRecordError δ η rs) * orderedReferenceWeight Q rs ≤
        orderedRecordWeight U S V rs x ∧
      orderedRecordWeight U S V rs x ≤
        Real.exp (orderedRecordError δ η rs) * orderedReferenceWeight Q rs := by
  intro rs
  induction rs with
  | nil =>
    intro x
    simpa only [orderedRecordError, orderedReferenceWeight, orderedRecordWeight, mul_one_div]
      using hV x
  | cons r rs ih =>
    have href := orderedReferenceWeight_nonneg Q hQ rs
    let lo := Real.exp (-orderedRecordError δ η rs) * orderedReferenceWeight Q rs
    let hi := Real.exp (orderedRecordError δ η rs) * orderedReferenceWeight Q rs
    have hlo : 0 ≤ lo := mul_nonneg (Real.exp_nonneg _) href
    have hhi : 0 ≤ hi := mul_nonneg (Real.exp_nonneg _) href
    have hf0 : ∀ y, 0 ≤ orderedRecordWeight U S V rs y := fun y ↦ hlo.trans (ih y).1
    have hfi (μ : Measure X) [IsFiniteMeasure μ] :
        Integrable (orderedRecordWeight U S V rs) μ := by
      apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable hi
      exact Filter.Eventually.of_forall (fun y ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (hf0 y)]
        exact (ih y).2)
    let g := fun z ↦ ∫ y, orderedRecordWeight U S V rs y ∂S z r
    have hg : ∀ z, lo * (Real.exp (-η r) * Q r) ≤ g z ∧
        g z ≤ hi * (Real.exp (η r) * Q r) := by
      intro z
      letI := hSf z r
      have hl := integral_mono (integrable_const lo) (hfi (S z r)) (fun y ↦ (ih y).1)
      have hu := integral_mono (hfi (S z r)) (integrable_const hi) (fun y ↦ (ih y).2)
      rw [integral_const, smul_eq_mul] at hl hu
      constructor
      · calc
          _ ≤ lo * (S z r).real Set.univ := mul_le_mul_of_nonneg_left (hS z r).1 hlo
          _ = (S z r).real Set.univ * lo := mul_comm _ _
          _ ≤ _ := hl
      · calc
          _ ≤ (S z r).real Set.univ * hi := hu
          _ = hi * (S z r).real Set.univ := mul_comm _ _
          _ ≤ _ := mul_le_mul_of_nonneg_left (hS z r).2 hhi
    have hg0 : ∀ z, 0 ≤ g z := fun z ↦
      (mul_nonneg hlo (mul_nonneg (Real.exp_nonneg _) (hQ r))).trans (hg z).1
    intro x
    letI := hUf x
    have hgi : Integrable g (U x) := by
      apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable
        (hi * (Real.exp (η r) * Q r))
      exact Filter.Eventually.of_forall (fun z ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (hg0 z)]
        exact (hg z).2)
    have hl := integral_mono (integrable_const (lo * (Real.exp (-η r) * Q r))) hgi
      (fun z ↦ (hg z).1)
    have hu := integral_mono hgi (integrable_const (hi * (Real.exp (η r) * Q r)))
      (fun z ↦ (hg z).2)
    rw [integral_const, smul_eq_mul] at hl hu
    have hlow : (Real.exp (-δ) / 2) * (lo * (Real.exp (-η r) * Q r)) ≤
        orderedRecordWeight U S V (r :: rs) x :=
      (mul_le_mul_of_nonneg_right (hU x).1
        (mul_nonneg hlo (mul_nonneg (Real.exp_nonneg _) (hQ r)))).trans hl
    have hupp : orderedRecordWeight U S V (r :: rs) x ≤
        (Real.exp δ / 2) * (hi * (Real.exp (η r) * Q r)) :=
      hu.trans (mul_le_mul_of_nonneg_right (hU x).2
        (mul_nonneg hhi (mul_nonneg (Real.exp_nonneg _) (hQ r))))
    have heL : Real.exp (-orderedRecordError δ η (r :: rs)) *
        orderedReferenceWeight Q (r :: rs) =
        (Real.exp (-δ) / 2) * (lo * (Real.exp (-η r) * Q r)) := by
      simp only [orderedRecordError, orderedReferenceWeight, neg_add, Real.exp_add, lo]
      ring
    have heU : Real.exp (orderedRecordError δ η (r :: rs)) *
        orderedReferenceWeight Q (r :: rs) =
        (Real.exp δ / 2) * (hi * (Real.exp (η r) * Q r)) := by
      simp only [orderedRecordError, orderedReferenceWeight, Real.exp_add, hi]
      ring
    exact ⟨heL ▸ hlow, heU ▸ hupp⟩

end SRWTightness
