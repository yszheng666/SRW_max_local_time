import SRWTightness.CountableProportionalAtomMass

open MeasureTheory
namespace SRWTightness

/-- Proportional joint event atoms sum to the original event probability. -/
theorem countable_event_proportional_mass {Ω R : Type*} [MeasurableSpace Ω]
    [MeasurableSpace R] [MeasurableSingletonClass R] [Countable R]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ν : Measure R) [IsProbabilityMeasure ν]
    (f : Ω → R) (hf : Measurable f) (E : Set Ω) (A : ℝ) (hA : 0 ≤ A)
    (h : ∀ r, μ.real {ω | f ω = r ∧ ω ∈ E} = A * ν.real {r}) : μ.real E = A := by
  let κ := (μ.restrict E).map f
  have hatom (r : R) : κ.real {r} = A * ν.real {r} := by
    rw [show κ = (μ.restrict E).map f from rfl,
      map_measureReal_apply hf (measurableSet_singleton r)]
    unfold Measure.real
    rw [Measure.restrict_apply (hf (measurableSet_singleton r))]
    exact h r
  have ht := countable_proportional_atom_mass κ ν A hA hatom
  simpa only [κ, Measure.real, Measure.map_apply hf MeasurableSet.univ,
    Set.preimage_univ, Measure.restrict_apply_univ] using ht

end SRWTightness
