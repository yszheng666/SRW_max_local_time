import SRWTightness.FiniteRecordErrorCount
import SRWTightness.GeometricGWLaw

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- Population record with terminal generation first, matching geometricGWRecordLaw. -/
def finiteRecordPopulationList {M : Type*} (n : ℕ) (r : FiniteExcursionRecord M n) :
    GeometricGWRecord :=
  List.ofFn (fun j : Fin (n + 1) ↦ finiteRecordLevelPopulation n r j)

/-- Countable marked-tree event mass given by the existing geometric branching product. -/
noncomputable def finiteRecordReferenceMass {M : Type*} [MeasurableSpace M]
    (μ : Measure M) (n : ℕ) (s : Set (FiniteExcursionRecord M n)) : ℝ≥0∞ := by
  classical
  exact ∑' r, if r ∈ s then
    ENNReal.ofReal (finiteRecordReferenceWeight (fun v ↦ μ.real {v}) n r) else 0

/-- Standard branching-product/population-law input, with independent probability-law leaf marks. -/
def MarkedGWTreeInput (M : Type*) [MeasurableSpace M] [MeasurableSingletonClass M]
    [Countable M] : Prop :=
  ∀ μ : Measure M, IsProbabilityMeasure μ → ∀ (n : ℕ) (s : Set GeometricGWRecord),
    finiteRecordReferenceMass μ n {r | finiteRecordPopulationList n r ∈ s} =
      geometricGWRecordLaw 1 n s

/-- Single-tree mass is precisely the previously used branching product. -/
theorem finiteRecordReferenceMass_singleton {M : Type*} [MeasurableSpace M]
    (μ : Measure M) (n : ℕ) (r : FiniteExcursionRecord M n) :
    finiteRecordReferenceMass μ n {r} =
      ENNReal.ofReal (finiteRecordReferenceWeight (fun v ↦ μ.real {v}) n r) := by
  classical
  unfold finiteRecordReferenceMass
  rw [tsum_eq_single r]
  · simp
  · intro v hv
    simp [hv]

/-- The real single-tree mass is exactly the weight in the actual record comparison. -/
theorem finiteRecordReferenceMass_singleton_toReal {M : Type*} [MeasurableSpace M]
    (μ : Measure M) (n : ℕ) (r : FiniteExcursionRecord M n) :
    (finiteRecordReferenceMass μ n {r}).toReal =
      finiteRecordReferenceWeight (fun v ↦ μ.real {v}) n r := by
  rw [finiteRecordReferenceMass_singleton, ENNReal.toReal_ofReal
    (finiteRecordReferenceWeight_nonneg _ (fun _ ↦ measureReal_nonneg) n r)]

/-- The standard population-law input also guarantees normalization of all tree weights. -/
theorem markedGWTree_mass_one {M : Type*} [MeasurableSpace M] [MeasurableSingletonClass M]
    [Countable M] (hinput : MarkedGWTreeInput M) (μ : Measure M)
    (hμ : IsProbabilityMeasure μ) (n : ℕ) :
    finiteRecordReferenceMass μ n Set.univ = 1 := by
  have hh := hinput μ hμ n Set.univ
  simpa only [Set.mem_univ, Set.setOf_true, measure_univ] using hh

/-- Population events of the marked tree have the actual finite-generation GW law. -/
theorem markedGWTree_population_law {M : Type*} [MeasurableSpace M]
    [MeasurableSingletonClass M] [Countable M] (hinput : MarkedGWTreeInput M)
    (μ : Measure M) (hμ : IsProbabilityMeasure μ) (n : ℕ) (s : Set GeometricGWRecord) :
    finiteRecordReferenceMass μ n {r | finiteRecordPopulationList n r ∈ s} =
      geometricGWRecordLaw 1 n s :=
  hinput μ hμ n s

end SRWTightness
