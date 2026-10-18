import SRWTightness.UniformGridIncrementControl
import Mathlib.MeasureTheory.Integral.Indicator

open MeasureTheory Filter
open scoped Topology
namespace SRWTightness

/-- For a process with continuous sample paths,
the probability of a large mesh increment vanishes. -/
theorem continuous_grid_increment_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : ℝ → Ω → ℝ)
    (hm : ∀ t, Measurable (X t)) (a b δ : ℝ) (hab : a ≤ b) (hδ : 0 < δ)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Set.Icc a b)) :
    Tendsto (fun n : ℕ ↦ μ.real {ω | ∃ j < 2 ^ n,
      δ < X (stoppedUniformTimeGrid a b (2 ^ n) (j + 1)) ω -
        X (stoppedUniformTimeGrid a b (2 ^ n) j) ω}) atTop (nhds 0) := by
  let E : ℕ → Set Ω := fun n ↦ {ω | ∃ j < 2 ^ n,
    δ < X (stoppedUniformTimeGrid a b (2 ^ n) (j + 1)) ω -
      X (stoppedUniformTimeGrid a b (2 ^ n) j) ω}
  have hE (n : ℕ) : MeasurableSet (E n) := by
    simp only [E, Set.setOf_exists]
    apply MeasurableSet.iUnion
    intro j
    by_cases hj : j < 2 ^ n
    · simpa only [hj, true_and, Pi.sub_apply] using
        (measurableSet_lt measurable_const
          ((hm (stoppedUniformTimeGrid a b (2 ^ n) (j + 1))).sub
            (hm (stoppedUniformTimeGrid a b (2 ^ n) j))))
    · simp only [hj, false_and, Set.setOf_false, MeasurableSet.empty]
  have he : ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, ω ∈ E n ↔ ω ∈ (∅ : Set Ω) := by
    filter_upwards [hc] with ω hω
    filter_upwards [continuous_dyadic_grid_small_increments (fun t ↦ X t ω)
      a b δ hab hω hδ] with n hn
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨j, hj, hlarge⟩
    have hs := hn j
    rw [Real.dist_eq] at hs
    exact (not_lt_of_ge ((le_abs_self _).trans hs.le)) hlarge
  have hlim := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
    atTop MeasurableSet.empty hE he
  have ht := (ENNReal.continuousAt_toReal (measure_ne_top μ (∅ : Set Ω))).tendsto.comp hlim
  simpa only [Measure.real, Function.comp_def, measure_empty, ENNReal.toReal_zero, E] using ht

end SRWTightness
