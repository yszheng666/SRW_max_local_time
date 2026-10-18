import SRWTightness.LabeledRootCountMixture
import SRWTightness.IndependentForestLaw
import SRWTightness.SourceExteriorRecordForests
import Mathlib.MeasureTheory.Measure.Dirac

open MeasureTheory
open scoped BigOperators
namespace SRWTightness

instance taggedForestValue_measurableSingletonClass {α β : Type*}
    [MeasurableSpace (List α)] [MeasurableSpace (List β)]
    [MeasurableSingletonClass (List α)] [MeasurableSingletonClass (List β)] :
    MeasurableSingletonClass (Sum (List α) (List β)) := ⟨by
  intro r
  cases r with
  | inl rs => simpa only [Set.image_singleton] using (measurableSet_singleton rs).inl_image
  | inr rs => simpa only [Set.image_singleton] using (measurableSet_singleton rs).inr_image⟩

/-- A nonempty block has a positive geometric count and independent ordered root atoms. -/
noncomputable def orderedForestBlockWeight {α : Type*} [MeasurableSpace α]
    (p : ℝ) (μ : Measure α) (rs : List α) : ℝ :=
  if rs = [] then 0 else p * (1 - p) ^ (rs.length - 1) *
    (rs.map (fun r ↦ μ.real {r})).prod

/-- Every block has the prescribed site label and a positive number of roots. -/
def orderedTaggedCompatible {α β : Type*} {n : ℕ} (label : Fin n → Bool)
    (r : Fin n → Sum (List α) (List β)) : Prop :=
  ∀ i, (r i).elim (fun rs ↦ label i = false ∧ rs ≠ [])
    (fun rs ↦ label i = true ∧ rs ≠ [])

/-- The two ordered concatenated forests extracted from the tagged block tuple. -/
def orderedTaggedForests {α β : Type*} {n : ℕ}
    (r : Fin n → Sum (List α) (List β)) : List α × List β :=
  (taggedForestLeft (List.ofFn r), taggedForestRight (List.ofFn r))

/-- The reference atom restricted to the prescribed two root totals. -/
noncomputable def orderedTaggedCountWeight {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {n : ℕ} (p : ℝ) (label : Fin n → Bool)
    (μ₀ : Measure α) (μ₁ : Measure β) (k l : ℕ)
    (r : Fin n → Sum (List α) (List β)) : ℝ := by
  classical
  exact if orderedTaggedCompatible label r ∧ (orderedTaggedForests r).1.length = k ∧
      (orderedTaggedForests r).2.length = l then
    ∏ i, (r i).elim (orderedForestBlockWeight p μ₀) (orderedForestBlockWeight p μ₁)
  else 0

/-- The atomic reference block measure with two fixed labeled root totals. -/
noncomputable def orderedTaggedCountMeasure {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace (List α)] [MeasurableSpace (List β)]
    {n : ℕ} (p : ℝ) (label : Fin n → Bool) (μ₀ : Measure α) (μ₁ : Measure β)
    (k l : ℕ) : Measure (Fin n → Sum (List α) (List β)) :=
  Measure.sum (fun r ↦ ENNReal.ofReal (orderedTaggedCountWeight p label μ₀ μ₁ k l r) •
    Measure.dirac r)

/-- The reference block atom is nonnegative for a geometric parameter. -/
theorem orderedForestBlockWeight_nonneg {α : Type*} [MeasurableSpace α]
    (p : ℝ) (μ : Measure α) (hp : 0 ≤ p) (hp₁ : p ≤ 1) (rs : List α) :
    0 ≤ orderedForestBlockWeight p μ rs := by
  classical
  unfold orderedForestBlockWeight
  split_ifs
  · exact le_rfl
  · apply mul_nonneg (mul_nonneg hp (pow_nonneg (sub_nonneg.mpr hp₁) _))
    exact List.prod_nonneg (by
      intro x hx
      obtain ⟨r, _, rfl⟩ := List.mem_map.mp hx
      exact measureReal_nonneg)

/-- All restricted tagged atom weights are nonnegative. -/
theorem orderedTaggedCountWeight_nonneg {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {n : ℕ} (p : ℝ) (label : Fin n → Bool)
    (μ₀ : Measure α) (μ₁ : Measure β) (k l : ℕ) (hp : 0 ≤ p) (hp₁ : p ≤ 1)
    (r : Fin n → Sum (List α) (List β)) :
    0 ≤ orderedTaggedCountWeight p label μ₀ μ₁ k l r := by
  classical
  unfold orderedTaggedCountWeight
  split_ifs
  · apply Finset.prod_nonneg
    intro i _
    cases r i with
    | inl rs => exact orderedForestBlockWeight_nonneg p μ₀ hp hp₁ rs
    | inr rs => exact orderedForestBlockWeight_nonneg p μ₁ hp hp₁ rs
  · exact le_rfl

/-- The atomic construction retains exactly the specified reference tuple weight. -/
theorem orderedTaggedCountMeasure_singleton {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace (List α)] [MeasurableSpace (List β)]
    [MeasurableSingletonClass (List α)] [MeasurableSingletonClass (List β)]
    {n : ℕ} (p : ℝ) (label : Fin n → Bool) (μ₀ : Measure α) (μ₁ : Measure β)
    (k l : ℕ) (r : Fin n → Sum (List α) (List β)) :
    orderedTaggedCountMeasure p label μ₀ μ₁ k l {r} =
      ENNReal.ofReal (orderedTaggedCountWeight p label μ₀ μ₁ k l r) := by
  exact Measure.sum_smul_dirac_singleton

end SRWTightness
