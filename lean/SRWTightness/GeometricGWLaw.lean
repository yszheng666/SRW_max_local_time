import Mathlib.Probability.Distributions.Geometric
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic.NormNum

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace SRWTightness

/-- The critical geometric offspring distribution, including zero offspring. -/
noncomputable def geometricGWOffspringLaw : Measure ℕ :=
  geometricMeasure ⟨1 / 2, by constructor <;> norm_num⟩

instance geometricGWOffspringLaw_isProbabilityMeasure : IsProbabilityMeasure geometricGWOffspringLaw := by
  unfold geometricGWOffspringLaw
  infer_instance

theorem geometricGWOffspringLaw_singleton (n : ℕ) :
    geometricGWOffspringLaw.real {n} = (1 / 2 : ℝ) ^ (n + 1) := by
  rw [geometricGWOffspringLaw, geometricMeasure_real_singleton (by
    intro h
    have hh := congrArg (fun p : unitInterval ↦ (p : ℝ)) h
    norm_num at hh)]
  norm_num [pow_succ]

/-- One generation is the sum of independently sampled offspring of all current individuals. -/
noncomputable def geometricGWGenerationLaw (k : ℕ) : Measure ℕ :=
  (Measure.pi (fun _ : Fin k ↦ geometricGWOffspringLaw)).map (fun ξ ↦ ∑ i, ξ i)

instance geometricGWGenerationLaw_isProbabilityMeasure (k : ℕ) :
    IsProbabilityMeasure (geometricGWGenerationLaw k) := by
  unfold geometricGWGenerationLaw
  exact Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

/-- A finite generation record, stored with the most recent generation first. -/
def GeometricGWRecord := List ℕ

instance : Countable GeometricGWRecord := inferInstanceAs (Countable (List ℕ))
instance : MeasurableSpace GeometricGWRecord := ⊤
instance : MeasurableSingletonClass GeometricGWRecord := ⟨fun _ ↦ trivial⟩

/-- Extend a record by one generation using fresh independent offspring. -/
noncomputable def geometricGWRecordStep (r : GeometricGWRecord) : Measure GeometricGWRecord :=
  (geometricGWGenerationLaw (r.headD 0)).map (fun n ↦ n :: r)

instance geometricGWRecordStep_isProbabilityMeasure (r : GeometricGWRecord) :
    IsProbabilityMeasure (geometricGWRecordStep r) := by
  unfold geometricGWRecordStep
  exact Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

/-- Exact finite-horizon critical geometric Galton--Watson law started with k individuals. -/
noncomputable def geometricGWRecordLaw (k : ℕ) : ℕ → Measure GeometricGWRecord
  | 0 => Measure.dirac (α := GeometricGWRecord) [k]
  | L + 1 => (geometricGWRecordLaw k L).bind geometricGWRecordStep

instance geometricGWRecordLaw_isProbabilityMeasure (k L : ℕ) :
    IsProbabilityMeasure (geometricGWRecordLaw k L) := by
  induction L with
  | zero => change IsProbabilityMeasure (Measure.dirac (α := GeometricGWRecord) [k]); infer_instance
  | succ L ih =>
    letI := ih
    change IsProbabilityMeasure ((geometricGWRecordLaw k L).bind geometricGWRecordStep)
    exact isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable
      (Filter.Eventually.of_forall fun r ↦ inferInstance)

/-- Population at a prescribed generation, read in chronological order. -/
def geometricGWPopulation (r : GeometricGWRecord) (j : ℕ) : ℕ :=
  (r.reverse[j]?).getD 0

/-- Square-root coordinate used in the external barrier estimates. -/
noncomputable def geometricGWHeight (r : GeometricGWRecord) (j : ℕ) : ℝ :=
  Real.sqrt (2 * (geometricGWPopulation r j : ℝ))

end SRWTightness
