import SRWTightness.FutureIndependence

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- A disjoint collection of histories has total probability at most one. -/
theorem disjoint_history_mass_le_one (E : ℕ → Set Sample)
    (hE : ∀ n, MeasurableSet[history n] (E n)) (hd : Pairwise (fun n m ↦ Disjoint (E n) (E m))) :
    (∑' n, pathLaw (E n)) ≤ 1 := by
  rw [← measure_iUnion hd (fun n ↦ (history.le n) _ (hE n))]
  exact prob_le_one

/-- A common future event factors out of a disjoint union of time-indexed histories. -/
theorem disjoint_history_future_mass (E : ℕ → Set Sample)
    (hE : ∀ n, MeasurableSet[history n] (E n)) (hd : Pairwise (fun n m ↦ Disjoint (E n) (E m)))
    (B : Set Sample) (hB : MeasurableSet B) :
    pathLaw (⋃ n, E n ∩ (shift n) ⁻¹' B) = (∑' n, pathLaw (E n)) * pathLaw B := by
  have hdis : Pairwise (fun n m ↦ Disjoint (E n ∩ (shift n) ⁻¹' B)
      (E m ∩ (shift m) ⁻¹' B)) := by
    intro n m hnm
    exact (hd hnm).mono Set.inter_subset_left Set.inter_subset_left
  rw [measure_iUnion hdis (fun n ↦
    ((history.le n) _ (hE n)).inter ((measurable_shift n) hB))]
  simp_rw [measure_past_inter_future _ _ _ (hE _) hB]
  exact ENNReal.tsum_mul_right

end SRWTightness
