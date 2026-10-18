import SRWTightness.FiniteFirstCrossing
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

open MeasureTheory
namespace SRWTightness

/-- The event that a sequence first reaches a level at the specified index. -/
def firstCrossingEvent {Ω : Type*} (W : ℕ → Ω → ℝ) (q : ℝ) (k : ℕ) : Set Ω :=
  {ω | q ≤ W k ω ∧ ∀ j < k, W j ω < q}

/-- First crossing at a fixed grid index is a measurable event. -/
theorem firstCrossingEvent_measurable {Ω : Type*} [MeasurableSpace Ω]
    (W : ℕ → Ω → ℝ) (hW : ∀ k, Measurable (W k)) (q : ℝ) (k : ℕ) :
    MeasurableSet (firstCrossingEvent W q k) := by
  simp only [firstCrossingEvent, Set.setOf_and, Set.setOf_forall]
  exact (measurableSet_le measurable_const (hW k)).inter
    (MeasurableSet.iInter (fun j ↦ MeasurableSet.iInter (fun _ : j < k ↦
      measurableSet_lt (hW j) measurable_const)))

/-- Distinct first crossing indices give disjoint events. -/
theorem firstCrossingEvent_disjoint {Ω : Type*} (W : ℕ → Ω → ℝ) (q : ℝ) :
    Pairwise (fun j k ↦ Disjoint (firstCrossingEvent W q j) (firstCrossingEvent W q k)) := by
  intro j k hjk
  apply Set.disjoint_left.mpr
  intro ω hj hk
  exact hjk (first_crossing_unique (fun i ↦ W i ω) q j k hj hk)

/-- The disjoint first crossing events cover precisely finite-grid crossing. -/
theorem firstCrossingEvent_union {Ω : Type*} (W : ℕ → Ω → ℝ) (q : ℝ) (n : ℕ) :
    (⋃ k : Fin (n + 1), firstCrossingEvent W q k) = {ω | ∃ k ≤ n, q ≤ W k ω} := by
  ext ω
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by omega, hk.1⟩
  · intro h
    obtain ⟨k, hkn, hk⟩ := finite_first_crossing (fun i ↦ W i ω) q n h
    exact ⟨⟨k, by omega⟩, hk⟩

end SRWTightness
