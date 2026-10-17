import SRWTightness.IndependentForestLaw
import SRWTightness.GeometricGWLaw

open MeasureTheory
open scoped ENNReal
namespace SRWTightness

/-- A geometric number of independently marked children, retaining their order. -/
noncomputable def geometricMarkedListLaw {M : Type*} [MeasurableSpace M]
    [MeasurableSpace (List M)] (μ : Measure M) : Measure (List M) :=
  Measure.sum (fun j : ℕ ↦ geometricGWOffspringLaw {j} • independentForestLaw μ j)

/-- The branching/mark mixture is a probability measure without a marked-tree input. -/
instance geometricMarkedListLaw_probability {M : Type*} [MeasurableSpace M]
    [MeasurableSpace (List M)] [MeasurableSingletonClass M] [Countable M]
    (μ : Measure M) [IsProbabilityMeasure μ] : IsProbabilityMeasure (geometricMarkedListLaw μ) := by
  constructor
  simp only [geometricMarkedListLaw, Measure.sum_apply _ MeasurableSet.univ,
    Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  have hh := congrArg (fun ν : Measure ℕ ↦ ν Set.univ)
    (Measure.sum_smul_dirac geometricGWOffspringLaw)
  simpa only [Measure.sum_apply _ MeasurableSet.univ, Measure.smul_apply,
    smul_eq_mul, measure_univ, mul_one] using hh

/-- A fixed-size independent list cannot assign mass to a list of a different size. -/
theorem independentForestLaw_singleton_wrong_length {M : Type*} [MeasurableSpace M]
    [MeasurableSpace (List M)] [MeasurableSingletonClass (List M)] [Countable M]
    (μ : Measure M) (j : ℕ) (rs : List M) (hlen : rs.length ≠ j) :
    independentForestLaw μ j {rs} = 0 := by
  unfold independentForestLaw
  by_cases hmap : AEMeasurable (List.ofFn : (Fin j → M) → List M)
      (Measure.pi (fun _ : Fin j ↦ μ))
  swap
  · rw [Measure.map_of_not_aemeasurable hmap]
    rfl
  rw [Measure.map_apply_of_aemeasurable hmap (measurableSet_singleton _)]
  have hp : List.ofFn ⁻¹' {rs} = (∅ : Set (Fin j → M)) := by
    ext f
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    intro hf
    apply hlen
    simpa only [List.length_ofFn] using (congrArg List.length hf).symm
  rw [hp, measure_empty]

/-- The constructed branching law has exactly the ordered record weight already used in
comparisons. -/
theorem geometricMarkedListLaw_singleton {M : Type*} [MeasurableSpace M]
    [MeasurableSpace (List M)] [MeasurableSingletonClass (List M)]
    [MeasurableSingletonClass M] [Countable M] (μ : Measure M) [IsProbabilityMeasure μ]
    (rs : List M) :
    geometricMarkedListLaw μ {rs} =
      ENNReal.ofReal (orderedReferenceWeight (fun v ↦ μ.real {v}) rs) := by
  classical
  simp only [geometricMarkedListLaw, Measure.sum_apply _ (measurableSet_singleton _),
    Measure.smul_apply, smul_eq_mul]
  rw [tsum_eq_single rs.length]
  · rw [independentForestLaw_singleton μ rs.length rs rfl]
    have hg : geometricGWOffspringLaw {rs.length} =
        ENNReal.ofReal ((1 / 2 : ℝ) ^ (rs.length + 1)) := by
      rw [← ofReal_measureReal (measure_ne_top geometricGWOffspringLaw _),
        geometricGWOffspringLaw_singleton]
    rw [hg, ← ENNReal.ofReal_mul (by positivity), orderedReferenceWeight_product]
  · intro j hj
    rw [independentForestLaw_singleton_wrong_length μ j rs (Ne.symm hj), mul_zero]

end SRWTightness
