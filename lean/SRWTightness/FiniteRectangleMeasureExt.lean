import Mathlib.MeasureTheory.Constructions.Pi

open MeasureTheory
namespace SRWTightness

/-- Finite measures on a finite product are determined by their measurable rectangles. -/
theorem finite_rectangle_measure_ext {ι : Type*} [Finite ι] {E : ι → Type*}
    [∀ i, MeasurableSpace (E i)] (μ ν : Measure (∀ i, E i)) [IsFiniteMeasure μ]
    (h : ∀ A : ∀ i, Set (E i), (∀ i, MeasurableSet (A i)) →
      μ (Set.pi Set.univ A) = ν (Set.pi Set.univ A)) : μ = ν := by
  apply ext_of_generate_finite _ generateFrom_pi.symm isPiSystem_pi
  · rintro _ ⟨A, hA, rfl⟩
    exact h A (fun i ↦ hA i (Set.mem_univ i))
  · simpa only [Set.pi_univ] using h (fun _ ↦ Set.univ) (fun _ ↦ MeasurableSet.univ)

end SRWTightness
