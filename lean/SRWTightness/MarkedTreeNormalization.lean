import SRWTightness.GeometricMarkedListLaw
import SRWTightness.FiniteRecordReferenceMeasure

open MeasureTheory
open scoped ENNReal
namespace SRWTightness

/-- Countable probability mass is the sum of its singleton masses. -/
theorem countable_probability_singleton_mass_sum {M : Type*} [MeasurableSpace M]
    [MeasurableSingletonClass M] [Countable M] (μ : Measure M) [IsProbabilityMeasure μ] :
    (∑' x : M, μ {x}) = 1 := by
  have hh := congrArg (fun ν : Measure M ↦ ν Set.univ) (Measure.sum_smul_dirac μ)
  simpa only [Measure.sum_apply _ MeasurableSet.univ, Measure.smul_apply,
    smul_eq_mul, measure_univ, mul_one] using hh

/-- Every normalized nonnegative countable child weight gives normalized ordered geometric
weights. -/
theorem ordered_reference_weight_mass_one {M : Type*} [Countable M] (Q : M → ℝ)
    (hQ : ∀ x, 0 ≤ Q x) (hSum : (∑' x : M, ENNReal.ofReal (Q x)) = 1) :
    (∑' rs : List M, ENNReal.ofReal (orderedReferenceWeight Q rs)) = 1 := by
  letI : MeasurableSpace M := ⊤
  letI : MeasurableSingletonClass M := ⟨fun _ ↦ trivial⟩
  letI : MeasurableSpace (List M) := ⊤
  letI : MeasurableSingletonClass (List M) := ⟨fun _ ↦ trivial⟩
  let μ : Measure M := Measure.sum (fun x : M ↦ ENNReal.ofReal (Q x) • Measure.dirac x)
  have hμ : IsProbabilityMeasure μ := by
    constructor
    simpa only [μ, Measure.sum_apply _ MeasurableSet.univ, Measure.smul_apply,
      smul_eq_mul, measure_univ, mul_one] using hSum
  letI := hμ
  have hsingle (x : M) : μ.real {x} = Q x := by
    change (μ {x}).toReal = Q x
    rw [show μ {x} = ENNReal.ofReal (Q x) from Measure.sum_smul_dirac_singleton]
    exact ENNReal.toReal_ofReal (hQ x)
  calc
    _ = ∑' rs : List M, geometricMarkedListLaw μ {rs} := by
      apply tsum_congr
      intro rs
      rw [geometricMarkedListLaw_singleton]
      simp only [hsingle]
    _ = 1 := countable_probability_singleton_mass_sum (geometricMarkedListLaw μ)

/-- Reference tree weights normalize at every depth without a branching/population-law input. -/
theorem finite_record_reference_weight_mass_one {M : Type*} [Countable M] (Q : M → ℝ)
    (hQ : ∀ x, 0 ≤ Q x) (hSum : (∑' x : M, ENNReal.ofReal (Q x)) = 1) :
    ∀ n : ℕ, (∑' r : FiniteExcursionRecord M n,
      ENNReal.ofReal (finiteRecordReferenceWeight Q n r)) = 1 := by
  intro n
  induction n with
  | zero => exact hSum
  | succ n ih =>
    letI := finiteExcursionRecord_countable M n
    exact ordered_reference_weight_mass_one (finiteRecordReferenceWeight Q n)
      (finiteRecordReferenceWeight_nonneg Q hQ n) ih

/-- The actual marked reference event mass is normalized internally on the whole tree space. -/
theorem finite_record_reference_mass_one_internal {M : Type*} [MeasurableSpace M]
    [MeasurableSingletonClass M] [Countable M] (μ : Measure M) [IsProbabilityMeasure μ]
    (n : ℕ) : finiteRecordReferenceMass μ n Set.univ = 1 := by
  have hsum : (∑' x : M, ENNReal.ofReal (μ.real {x})) = 1 := by
    simpa only [ofReal_measureReal (measure_ne_top μ _)] using
      countable_probability_singleton_mass_sum μ
  simpa only [finiteRecordReferenceMass, Set.mem_univ, if_true] using
    finite_record_reference_weight_mass_one (fun x ↦ μ.real {x})
      (fun _ ↦ measureReal_nonneg) hsum n

/-- The actual atomic marked-tree reference measure is a probability without MarkedGWTreeInput. -/
theorem finite_record_reference_measure_probability_internal {M : Type*} [MeasurableSpace M]
    [MeasurableSingletonClass M] [Countable M] (μ : Measure M) [IsProbabilityMeasure μ]
    (n : ℕ) [MeasurableSpace (FiniteExcursionRecord M n)]
    [MeasurableSingletonClass (FiniteExcursionRecord M n)] :
    IsProbabilityMeasure (finiteRecordReferenceMeasure μ n) := by
  constructor
  rw [finiteRecordReferenceMeasure_apply]
  exact finite_record_reference_mass_one_internal μ n

end SRWTightness
