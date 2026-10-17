import SRWTightness.ExternalMarkedGWForestJoint
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory
open scoped ENNReal
namespace SRWTightness

/-- The generic marked forest joint law extends to independent auxiliary variables by Tonelli. -/
theorem markedGWForestJoint_auxiliary {M Ξ : Type*} [MeasurableSpace M]
    [MeasurableSingletonClass M] [Countable M] [MeasurableSpace (List M)]
    [MeasurableSingletonClass (List M)] [MeasurableSpace Ξ]
    (hinput : MarkedGWForestJointInput M) (μ : Measure M) [IsProbabilityMeasure μ]
    (ν : Measure Ξ) [SFinite ν] (n k : ℕ)
    [MeasurableSpace (FiniteExcursionRecord M n)]
    [MeasurableSingletonClass (FiniteExcursionRecord M n)]
    [MeasurableSpace (List (FiniteExcursionRecord M n))]
    [MeasurableSingletonClass (List (FiniteExcursionRecord M n))]
    (s : Set GeometricGWRecord) (E : GeometricGWRecord → Set (List M × Ξ))
    (hE : ∀ g, MeasurableSet (E g)) :
    let S := {p : List (FiniteExcursionRecord M n) × Ξ |
      forestPopulationList n p.1 ∈ s ∧
      (p.1.flatMap (finiteRecordLeaves n), p.2) ∈ E (forestPopulationList n p.1)}
    MeasurableSet S →
    ((independentForestLaw (finiteRecordReferenceMeasure μ n) k).prod ν) S =
      ∫⁻ g in s, ((independentForestLaw μ (geometricGWPopulation g n)).prod ν) (E g)
        ∂geometricGWRecordLaw k n := by
  dsimp only
  intro hS
  letI := finiteExcursionRecord_countable M n
  letI := finiteRecordReferenceMeasure_probability (markedGWJoint_population hinput.singleRoot)
    μ inferInstance n
  rw [Measure.prod_apply_symm hS]
  have hsection (y : Ξ) :
      (independentForestLaw (finiteRecordReferenceMeasure μ n) k)
        ((fun x ↦ (x, y)) ⁻¹' {p | forestPopulationList n p.1 ∈ s ∧
          (p.1.flatMap (finiteRecordLeaves n), p.2) ∈ E (forestPopulationList n p.1)}) =
      ∫⁻ g in s, independentForestLaw μ (geometricGWPopulation g n)
        ((fun rs ↦ (rs, y)) ⁻¹' E g) ∂geometricGWRecordLaw k n :=
    hinput.forest μ inferInstance n k s (fun g ↦ (fun rs ↦ (rs, y)) ⁻¹' E g)
  simp_rw [hsection]
  have hm : Measurable (fun p : GeometricGWRecord × Ξ ↦
      independentForestLaw μ (geometricGWPopulation p.1 n)
        ((fun rs ↦ (rs, p.2)) ⁻¹' E p.1)) :=
    measurable_from_prod_countable_right (fun g ↦ measurable_measure_prodMk_right
      (μ := independentForestLaw μ (geometricGWPopulation g n)) (hE g))
  rw [← lintegral_lintegral_swap (μ := (geometricGWRecordLaw k n).restrict s)
    (ν := ν) (f := fun g y ↦ independentForestLaw μ (geometricGWPopulation g n)
      ((fun rs ↦ (rs, y)) ⁻¹' E g)) hm.aemeasurable]
  apply lintegral_congr
  intro g
  exact (Measure.prod_apply_symm (hE g)).symm

end SRWTightness
