import SRWTightness.ExternalMarkedGWJoint
import SRWTightness.FiniteRecordReferenceMeasure
import SRWTightness.SingleRootReferenceEvent
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- The marked-tree joint input extends to the same independent auxiliary space by Tonelli. -/
theorem markedGWJoint_auxiliary {M Ξ : Type*} [MeasurableSpace M]
    [MeasurableSingletonClass M] [Countable M] [MeasurableSpace (List M)]
    [MeasurableSingletonClass (List M)] [MeasurableSpace Ξ]
    (hinput : MarkedGWJointInput M) (μ : Measure M) [IsProbabilityMeasure μ]
    (ν : Measure Ξ) [SFinite ν] (n : ℕ)
    [MeasurableSpace (FiniteExcursionRecord M n)]
    [MeasurableSingletonClass (FiniteExcursionRecord M n)]
    [MeasurableSpace (List (FiniteExcursionRecord M n))]
    [MeasurableSingletonClass (List (FiniteExcursionRecord M n))]
    (s : Set GeometricGWRecord) (E : GeometricGWRecord → Set (List M × Ξ))
    (hE : ∀ g, MeasurableSet (E g)) :
    let S := {p : List (FiniteExcursionRecord M n) × Ξ | ∃ r, p.1 = [r] ∧
      finiteRecordPopulationList n r ∈ s ∧
      (finiteRecordLeaves n r, p.2) ∈ E (finiteRecordPopulationList n r)}
    MeasurableSet S →
    ((independentForestLaw (finiteRecordReferenceMeasure μ n) 1).prod ν) S =
      ∫⁻ g in s, ((independentForestLaw μ (geometricGWPopulation g n)).prod ν) (E g)
        ∂geometricGWRecordLaw 1 n := by
  dsimp only
  intro hS
  letI := finiteExcursionRecord_countable M n
  letI := finiteRecordReferenceMeasure_probability (markedGWJoint_population hinput)
    μ inferInstance n
  rw [Measure.prod_apply_symm hS]
  have hsection (y : Ξ) :
      (independentForestLaw (finiteRecordReferenceMeasure μ n) 1)
        ((fun x ↦ (x, y)) ⁻¹' {p | ∃ r, p.1 = [r] ∧
          finiteRecordPopulationList n r ∈ s ∧
          (finiteRecordLeaves n r, p.2) ∈ E (finiteRecordPopulationList n r)}) =
      ∫⁻ g in s, independentForestLaw μ (geometricGWPopulation g n)
        ((fun rs ↦ (rs, y)) ⁻¹' E g) ∂geometricGWRecordLaw 1 n := by
    have he : ((fun x ↦ (x, y)) ⁻¹' {p | ∃ r, p.1 = [r] ∧
          finiteRecordPopulationList n r ∈ s ∧
          (finiteRecordLeaves n r, p.2) ∈ E (finiteRecordPopulationList n r)}) =
        {rs | ∃ r ∈ {r | finiteRecordPopulationList n r ∈ s ∧
          (finiteRecordLeaves n r, y) ∈ E (finiteRecordPopulationList n r)}, rs = [r]} := by
      ext rs
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      constructor
      · rintro ⟨r, hr, hg, hmark⟩
        exact ⟨r, ⟨hg, hmark⟩, hr⟩
      · rintro ⟨r, ⟨hg, hmark⟩, hr⟩
        exact ⟨r, hr, hg, hmark⟩
    rw [he, independentForestLaw_single_root_event, finiteRecordReferenceMeasure_apply]
    exact hinput μ inferInstance n s (fun g ↦ (fun rs ↦ (rs, y)) ⁻¹' E g)
  simp_rw [hsection]
  have hm : Measurable (fun p : GeometricGWRecord × Ξ ↦
      independentForestLaw μ (geometricGWPopulation p.1 n)
        ((fun rs ↦ (rs, p.2)) ⁻¹' E p.1)) :=
    measurable_from_prod_countable_right (fun g ↦ measurable_measure_prodMk_right
      (μ := independentForestLaw μ (geometricGWPopulation g n)) (hE g))
  rw [← lintegral_lintegral_swap (μ := (geometricGWRecordLaw 1 n).restrict s)
    (ν := ν) (f := fun g y ↦ independentForestLaw μ (geometricGWPopulation g n)
      ((fun rs ↦ (rs, y)) ⁻¹' E g)) hm.aemeasurable]
  apply lintegral_congr
  intro g
  exact (Measure.prod_apply_symm (hE g)).symm

end SRWTightness
