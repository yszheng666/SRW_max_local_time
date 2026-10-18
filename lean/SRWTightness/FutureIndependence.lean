import SRWTightness.Shift
import SRWTightness.Filtration

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- All future increments are independent of the complete natural past. -/
theorem history_indep_future (n : ℕ) :
    Indep (history n) (MeasurableSpace.comap (shift n) inferInstance) pathLaw := by
  let m : ℕ → MeasurableSpace Sample := fun i ↦
    MeasurableSpace.comap (fun ω : Sample ↦ ω i) inferInstance
  have hd : Disjoint (Set.Iio n) (Set.Ici n) := by
    apply Set.disjoint_left.mpr
    intro i hi hj
    change i < n at hi
    change n ≤ i at hj
    omega
  have hind := indep_iSup_of_disjoint
    (m := m) (fun i ↦ (measurable_pi_apply i).comap_le)
    (show iIndep m pathLaw from directions_independent) hd
  apply indep_of_indep_of_le hind
  · change MeasurableSpace.comap (fun ω : Sample ↦ fun i : Finset.range n ↦ ω i)
      inferInstance ≤ _
    rw [MeasurableSpace.comap_process_pi]
    apply iSup_le
    intro i
    exact le_iSup_of_le (i : ℕ) (le_iSup_of_le (Finset.mem_range.mp i.property) le_rfl)
  · change MeasurableSpace.comap (fun ω : Sample ↦ fun k ↦ ω (n + k)) inferInstance ≤ _
    rw [MeasurableSpace.comap_process_pi]
    apply iSup_le
    intro k
    exact le_iSup_of_le (n + k) (le_iSup_of_le (Nat.le_add_right n k) le_rfl)

 theorem measure_past_inter_future (n : ℕ) (s t : Set Sample)
    (hs : MeasurableSet[history n] s) (ht : MeasurableSet t) :
    pathLaw (s ∩ (shift n) ⁻¹' t) = pathLaw s * pathLaw t := by
  have hi := (history_indep_future n).indepSet_of_measurableSet hs
    ((comap_measurable (shift n)) ht)
  rw [hi.measure_inter_eq_mul]
  rw [← Measure.map_apply (measurable_shift n) ht, shift_law]

end SRWTightness
