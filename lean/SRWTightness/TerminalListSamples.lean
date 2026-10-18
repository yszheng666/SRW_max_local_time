import SRWTightness.IndependentForestLaw
import SRWTightness.IndependentMarks
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory

namespace SRWTightness

/-- Read the first k ordered terminal marks, with an explicit value outside the list. -/
def terminalListSamples {M : Type*} (v : M) (k : ℕ) (rs : List M) : Fin k → M :=
  fun i ↦ (rs[i.val]?).getD v

/-- Reading the sampled list recovers every original mark, also for the empty product. -/
theorem terminalListSamples_ofFn {M : Type*} (v : M) (k : ℕ) (f : Fin k → M) :
    terminalListSamples v k (List.ofFn f) = f := by
  funext i
  simp [terminalListSamples]

/-- The ordered independent list recovers exactly the finite independent sample law. -/
theorem terminalListSamples_law {M : Type*} [MeasurableSpace M]
    [MeasurableSingletonClass M] [Countable M] [MeasurableSpace (List M)]
    [MeasurableSingletonClass (List M)] (μ : Measure M) (v : M) (k : ℕ) :
    (independentForestLaw μ k).map (terminalListSamples v k) =
      Measure.pi (fun _ : Fin k ↦ μ) := by
  rw [independentForestLaw, Measure.map_map (measurable_of_countable _)
    (measurable_of_countable _)]
  have he : terminalListSamples v k ∘ List.ofFn = id := by
    funext f
    exact terminalListSamples_ofFn v k f
  rw [he, Measure.map_id]

/-- Decoding the ordered marks preserves their joint law with any independent auxiliary space. -/
theorem terminalListSamples_product_law {M Ξ : Type*} [MeasurableSpace M]
    [MeasurableSingletonClass M] [Countable M] [MeasurableSpace (List M)]
    [MeasurableSingletonClass (List M)] [MeasurableSpace Ξ]
    (μ : Measure M) [IsProbabilityMeasure μ] (ν : Measure Ξ) [SFinite ν]
    (v : M) (k : ℕ) :
    ((independentForestLaw μ k).prod ν).map
      (Prod.map (terminalListSamples v k) id) =
        (Measure.pi (fun _ : Fin k ↦ μ)).prod ν := by
  rw [← Measure.map_prod_map _ _ (measurable_of_countable _) measurable_id,
    terminalListSamples_law, Measure.map_id]

end SRWTightness
