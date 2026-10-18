import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

open MeasureTheory Filter
open scoped Topology
namespace SRWTightness

/-- A continuous barrier distribution gives the same probability for strict and closed tests. -/
theorem strict_barrier_of_continuous_distribution {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : ι → Ω → ℝ) (F : ℝ → ℝ)
    (q : ℝ) (hq : 0 < q) (hF : ContinuousAt F q)
    (hclosed : ∀ p, 0 < p → μ.real {ω | ∀ i, X i ω ≤ p} = F p) :
    μ.real {ω | ∀ i, X i ω < q} = F q := by
  apply le_antisymm
  · rw [← hclosed q hq]
    exact measureReal_mono (fun ω hω i ↦ (hω i).le)
  · have hlim : Tendsto (fun n : ℕ ↦ q - 1 / ((n : ℝ) + 1)) atTop (nhds q) := by
      simpa only [sub_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ q) atTop (nhds q)).sub
          tendsto_one_div_add_atTop_nhds_zero_nat
    apply le_of_tendsto (hF.tendsto.comp hlim)
    filter_upwards [hlim.eventually (Ioi_mem_nhds hq)] with n hn
    change F (q - 1 / ((n : ℝ) + 1)) ≤ _
    rw [← hclosed _ hn]
    refine measureReal_mono ?_ (measure_ne_top _ _)
    intro ω hω i
    have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hh := hω i
    linarith

end SRWTightness
