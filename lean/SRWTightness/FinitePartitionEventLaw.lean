import Mathlib.MeasureTheory.Measure.Real

open MeasureTheory
namespace SRWTightness

/-- Event-law identities on disjoint finite pieces combine without any independence assumption. -/
theorem finite_partition_event_law {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsFiniteMeasure μ] (A F : ι → Set Ω) (E : Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (hF : ∀ i, MeasurableSet (F i))
    (hE : MeasurableSet E) (hd : Pairwise (fun i j ↦ Disjoint (A i) (A j)))
    (he : ∀ i, μ.real (A i ∩ E) = μ.real (A i ∩ F i)) :
    μ.real ((⋃ i, A i) ∩ E) = μ.real (⋃ i, A i ∩ F i) := by
  rw [Set.iUnion_inter]
  rw [measureReal_iUnion_fintype
    (fun i j hij ↦ (hd hij).mono Set.inter_subset_left Set.inter_subset_left)
    (fun i ↦ (hA i).inter hE),
    measureReal_iUnion_fintype
      (fun i j hij ↦ (hd hij).mono Set.inter_subset_left Set.inter_subset_left)
      (fun i ↦ (hA i).inter (hF i))]
  exact Finset.sum_congr rfl (fun i _ ↦ he i)

end SRWTightness
