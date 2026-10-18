import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Analysis.SpecificLimits.Basic

open MeasureTheory Filter
open scoped Topology
namespace SRWTightness

/-- Increasing event probabilities inherit an exact continuous tail formula
from vanishing errors. -/
theorem monotone_event_probability_squeeze {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (E : ℕ → Set Ω) (hmono : Monotone E)
    (g : ℝ → ℝ) (hg : ContinuousAt g 0) (e : ℝ → ℕ → ℝ)
    (he : ∀ δ > 0, Tendsto (e δ) atTop (nhds 0))
    (hu : ∀ n, μ.real (E n) ≤ g 0)
    (hl : ∀ δ > 0, ∀ n, g δ - e δ n ≤ μ.real (E n)) :
    μ.real (⋃ n, E n) = g 0 := by
  have hlim : Tendsto (fun n ↦ μ.real (E n)) atTop (nhds (μ.real (⋃ n, E n))) := by
    simpa only [Measure.real, Function.comp_def] using
      (ENNReal.continuousAt_toReal (measure_ne_top μ _)).tendsto.comp
        (tendsto_measure_iUnion_atTop (μ := μ) hmono)
  apply le_antisymm
  · exact le_of_tendsto hlim (Eventually.of_forall hu)
  · have hlow (δ : ℝ) (hδ : 0 < δ) : g δ ≤ μ.real (⋃ n, E n) := by
      have ht : Tendsto (fun n ↦ g δ - e δ n) atTop (nhds (g δ)) := by
        simpa only [sub_zero] using (tendsto_const_nhds.sub (he δ hδ))
      exact le_of_tendsto_of_tendsto ht hlim (Eventually.of_forall (hl δ hδ))
    have ht : Tendsto (fun n : ℕ ↦ g (1 / ((n : ℝ) + 1))) atTop (nhds (g 0)) :=
      hg.tendsto.comp tendsto_one_div_add_atTop_nhds_zero_nat
    exact le_of_tendsto ht (Eventually.of_forall (fun n ↦ hlow _ (by positivity)))

end SRWTightness
