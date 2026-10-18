import SRWTightness.CommonGWEndpointIntegral
import SRWTightness.CommonPairListHighEvent
import SRWTightness.ExternalMarkedGWJoint
import Mathlib.Data.ENNReal.BigOperators

open MeasureTheory
open scoped BigOperators ENNReal
namespace SRWTightness

/-- The joint marked reference event is bounded by the exact finite GW-weighted mark sum. -/
theorem common_marked_reference_endpoint_sum (D K A : Finset Site) (hAK : A ⊆ K)
    (α level q : ℝ) (j : ℕ) (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1) (hq : 0 ≤ q)
    [MeasurableSpace (List (Mark K))] [MeasurableSingletonClass (List (Mark K))]
    (hinput : MarkedGWJointInput (Mark K))
    (s : Set GeometricGWRecord) (hs : ∀ r ∈ s, geometricGWHeight r j ≤ q) :
    finiteRecordReferenceMass (referenceMarkLaw D K α) j
      {r | finiteRecordPopulationList j r ∈ s ∧
        finiteRecordLeaves j r ∈ commonPairListHighEvent K A hAK
          (geometricGWPopulation (finiteRecordPopulationList j r) j) level} ≤
      ENNReal.ofReal (∑ k ∈ Finset.range (⌊q ^ 2 / 2⌋₊ + 1),
        (geometricGWRecordLaw 1 j).real {r | geometricGWPopulation r j = k} *
        (markProductLaw D K α k).real
          {Y | ∀ v : A, level ≤ (sumMarks K k Y ⟨v, hAK v.property⟩ : ℝ)}) := by
  rw [hinput _ (referenceMarkLaw_isProbabilityMeasure D K α hα hcap) j s
    (fun g ↦ commonPairListHighEvent K A hAK (geometricGWPopulation g j) level)]
  simp_rw [common_pair_list_high_probability]
  have hh := common_gw_endpoint_integral_upper j q hq s hs
    (fun k ↦ markProductLaw D K α k
      {Y | ∀ v : A, level ≤ (sumMarks K k Y ⟨v, hAK v.property⟩ : ℝ)})
  apply hh.trans_eq
  rw [ENNReal.ofReal_sum_of_nonneg (by intro k hk; positivity)]
  apply Finset.sum_congr rfl
  intro k hk
  letI := markProductLaw_isProbabilityMeasure D K α hα hcap k
  rw [ENNReal.ofReal_mul (measureReal_nonneg),
    ofReal_measureReal (measure_ne_top (geometricGWRecordLaw 1 j) _),
    ofReal_measureReal (measure_ne_top (markProductLaw D K α k) _)]
  exact mul_comm _ _

end SRWTightness
