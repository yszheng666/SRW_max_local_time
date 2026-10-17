import SRWTightness.ExponentialSumTail
import SRWTightness.ContinuousOccupation

open MeasureTheory ProbabilityTheory

namespace SRWTightness

 theorem holdingKernel_coordinate_ge_count (A : Finset Site) (Y : Mark A) (z : A)
    (hz : 0 < Y z) :
    (1 / 36 : ℝ) ≤ (holdingKernel A Y).real {L : A → ℝ | (Y z : ℝ) ≤ L z} := by
  have hj : Function.Injective (fun i : Fin (Y z) ↦ (⟨z, i⟩ : HoldingIndex Y)) := by
    intro i j h
    exact Sigma.mk.inj_iff.mp h |>.2 |> eq_of_heq
  have ht := exponential_selected_sum_ge_card
    (fun i : Fin (Y z) ↦ (⟨z, i⟩ : HoldingIndex Y)) hj (by simpa using hz)
  change (1 / 36 : ℝ) ≤ ((holdingTimeLaw Y).map (continuousMark Y)).real _
  rw [measureReal_def, Measure.map_apply (measurable_continuousMark Y)
    (measurableSet_le measurable_const (measurable_pi_apply z))]
  simpa only [Fintype.card_fin, holdingTimeLaw, continuousMark, measureReal_def,
    Set.preimage_setOf_eq] using ht

 def continuousExceedance (A : Finset Site) (a : ℕ) : Set (A → ℝ) :=
  {L | ∃ z : A, (a : ℝ) ≤ L z}

 theorem measurableSet_continuousExceedance (A : Finset Site) (a : ℕ) :
    MeasurableSet (continuousExceedance A a) := by
  unfold continuousExceedance
  rw [Set.setOf_exists]
  exact MeasurableSet.iUnion (fun z ↦ measurableSet_le measurable_const (measurable_pi_apply z))

/-- Once a discrete coordinate exceeds a, an exponential occupation exceeds the same a
with probability at least 1/36. The estimate does not depend on the number of coordinates. -/
theorem holdingKernel_max_exceedance_lower (A : Finset Site) (Y : Mark A)
    (a : ℕ) (ha : 1 ≤ a) (hY : ∃ z : A, a ≤ Y z) :
    (1 / 36 : ℝ) ≤ (holdingKernel A Y).real (continuousExceedance A a) := by
  obtain ⟨z, hz⟩ := hY
  have hypos : 0 < Y z := lt_of_lt_of_le (by omega : 0 < a) hz
  apply (holdingKernel_coordinate_ge_count A Y z hypos).trans
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro L hL
  exact ⟨z, (by exact_mod_cast hz : (a : ℝ) ≤ Y z).trans hL⟩

 theorem count_indicator_le_holding_exceedance (A : Finset Site) (a : ℕ) (ha : 1 ≤ a)
    (Y : Mark A) :
    ({Y : Mark A | ∃ z : A, a ≤ Y z}.indicator (fun _ ↦ (1 : ℝ))) Y ≤
      36 * (holdingKernel A Y).real (continuousExceedance A a) := by
  by_cases hY : ∃ z : A, a ≤ Y z
  · rw [Set.indicator_of_mem (show Y ∈ {Y : Mark A | ∃ z : A, a ≤ Y z} from hY)]
    have hb := holdingKernel_max_exceedance_lower A Y a ha hY
    linarith
  · rw [Set.indicator_of_notMem (show Y ∉ {Y : Mark A | ∃ z : A, a ≤ Y z} from hY)]
    positivity

end SRWTightness
