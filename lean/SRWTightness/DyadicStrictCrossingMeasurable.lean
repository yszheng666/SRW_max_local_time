import SRWTightness.ContinuousDyadicGridCrossing
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

open MeasureTheory
namespace SRWTightness

/-- Strict crossing on the countable union of uniform dyadic grids is measurable. -/
theorem uniform_dyadic_strict_crossing_measurable {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ → Ω → ℝ) (hm : ∀ t, Measurable (X t)) (a b q : ℝ) :
    MeasurableSet {ω | ∃ n : ℕ, ∃ k ≤ 2 ^ n,
      q < X (stoppedUniformTimeGrid a b (2 ^ n) k) ω} := by
  simp only [Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.iUnion
  intro k
  by_cases hk : k ≤ 2 ^ n
  · simpa only [hk, true_and] using
      (measurableSet_lt (measurable_const (a := q)) (hm (stoppedUniformTimeGrid a b (2 ^ n) k)))
  · simp only [hk, false_and, Set.setOf_false, MeasurableSet.empty]

end SRWTightness
