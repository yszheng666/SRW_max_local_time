import SRWTightness.OrderedRecordComparison

open MeasureTheory

namespace SRWTightness

/-- The first-entrance/root-record/final-nonreturn integral for exactly one root. -/
noncomputable def singleRootRecordWeight {X : Type*} [MeasurableSpace X]
    (I : Measure X) (S : X → Measure X) (q : X → ℝ) : ℝ :=
  ∫ x, ∫ y, q y ∂S x ∂I

/-- The single-root comparison retains the exit-dependent nonreturn factor. -/
theorem single_root_record_comparison {X : Type*} [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (I : Measure X) [IsFiniteMeasure I] (S : X → Measure X)
    (hSf : ∀ x, IsFiniteMeasure (S x)) (q : X → ℝ) (c₁ c₂ η Q : ℝ)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hQ : 0 ≤ Q)
    (hI : c₁ ≤ I.real Set.univ ∧ I.real Set.univ ≤ 1)
    (hq : ∀ y, c₂ ≤ q y ∧ q y ≤ 1)
    (hS : ∀ x, Real.exp (-η) * Q ≤ (S x).real Set.univ ∧
      (S x).real Set.univ ≤ Real.exp η * Q) :
    c₁ * c₂ * Real.exp (-η) * Q ≤ singleRootRecordWeight I S q ∧
      singleRootRecordWeight I S q ≤ Real.exp η * Q := by
  let f := fun x ↦ ∫ y, q y ∂S x
  have hq0 : ∀ y, 0 ≤ q y := fun y ↦ hc₂.trans (hq y).1
  have hf : ∀ x, c₂ * (Real.exp (-η) * Q) ≤ f x ∧ f x ≤ Real.exp η * Q := by
    intro x
    letI := hSf x
    have hqi : Integrable q (S x) := by
      apply Integrable.of_bound (measurable_of_countable q).aestronglyMeasurable 1
      exact Filter.Eventually.of_forall (fun y ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (hq0 y)]
        exact (hq y).2)
    have hl := integral_mono (integrable_const c₂) hqi (fun y ↦ (hq y).1)
    have hu := integral_mono hqi (integrable_const (1 : ℝ)) (fun y ↦ (hq y).2)
    rw [integral_const, smul_eq_mul] at hl hu
    constructor
    · calc
        _ ≤ c₂ * (S x).real Set.univ := mul_le_mul_of_nonneg_left (hS x).1 hc₂
        _ = (S x).real Set.univ * c₂ := mul_comm _ _
        _ ≤ _ := hl
    · simpa only [mul_one] using hu.trans (by simpa only [mul_one] using (hS x).2)
  have hf0 : ∀ x, 0 ≤ f x := fun x ↦
    (mul_nonneg hc₂ (mul_nonneg (Real.exp_nonneg _) hQ)).trans (hf x).1
  have hfi : Integrable f I := by
    apply Integrable.of_bound (measurable_of_countable f).aestronglyMeasurable (Real.exp η * Q)
    exact Filter.Eventually.of_forall (fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 x)]
      exact (hf x).2)
  have hl := integral_mono (integrable_const (c₂ * (Real.exp (-η) * Q))) hfi
    (fun x ↦ (hf x).1)
  have hu := integral_mono hfi (integrable_const (Real.exp η * Q)) (fun x ↦ (hf x).2)
  rw [integral_const, smul_eq_mul] at hl hu
  constructor
  · calc
      _ = c₁ * (c₂ * (Real.exp (-η) * Q)) := by ring
      _ ≤ I.real Set.univ * (c₂ * (Real.exp (-η) * Q)) :=
        mul_le_mul_of_nonneg_right hI.1 (by positivity)
      _ ≤ _ := hl
  · calc
      _ ≤ I.real Set.univ * (Real.exp η * Q) := hu
      _ ≤ 1 * (Real.exp η * Q) := mul_le_mul_of_nonneg_right hI.2 (by positivity)
      _ = _ := one_mul _

end SRWTightness
