import SRWTightness.FiniteKilledChainWordLaw

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

attribute [local instance] finiteChainListMeasurableSpace finiteChainListMeasurableSingleton

/-- The actual joint trace/exit event in the killed-path law equals its path-sum mass. -/
theorem finiteChainKilledWordLaw_trace_exit {σ : Type*} [MeasurableSpace σ]
    [MeasurableSingletonClass σ] [Countable σ]
    (P : σ → σ → ℝ≥0∞) (D K : Set σ) [DecidablePred (· ∈ K)]
    (x : σ) (e : {y : σ // y ∉ D}) (as : List D) :
    finiteChainKilledWordLaw P D x
      {q | q.1.filter (fun a : D ↦ decide (a.val ∈ K)) = as ∧ q.2 = e} =
      finiteChainTraceExitMass P D K x e.val as := by
  classical
  rw [finiteChainKilledWordLaw, Measure.sum_apply _ (Set.to_countable _).measurableSet]
  simp only [Measure.smul_apply, Measure.dirac_apply, Set.indicator_apply,
    Set.mem_setOf_eq, Pi.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [ENNReal.tsum_prod']
  unfold finiteChainTraceExitMass filteredWordMass FilteredWordFiber
  trans ∑' w : List D, if w.filter (fun a : D ↦ decide (a.val ∈ K)) = as then
    chainWordWeight P Subtype.val x w e.val else 0
  · apply tsum_congr
    intro w
    by_cases hw : w.filter (fun a : D ↦ decide (a.val ∈ K)) = as <;> simp [hw]
  · convert (tsum_subtype {w : List D | w.filter (fun a : D ↦ decide (a.val ∈ K)) = as}
      (fun w ↦ chainWordWeight P Subtype.val x w e.val)).symm using 1 <;>
      simp only [Set.indicator_apply, Set.mem_setOf_eq] <;> try rfl

/-- The actual finite trace event is the sum over all possible exit states. -/
theorem finiteChainKilledWordLaw_trace {σ : Type*} [MeasurableSpace σ]
    [MeasurableSingletonClass σ] [Countable σ]
    (P : σ → σ → ℝ≥0∞) (D K : Set σ) [DecidablePred (· ∈ K)]
    (x : σ) (as : List D) :
    finiteChainKilledWordLaw P D x
      {q | q.1.filter (fun a : D ↦ decide (a.val ∈ K)) = as} =
      finiteChainTraceMass P D K x as := by
  classical
  rw [finiteChainKilledWordLaw, Measure.sum_apply _ (Set.to_countable _).measurableSet]
  simp only [Measure.smul_apply, Measure.dirac_apply, Set.indicator_apply,
    Set.mem_setOf_eq, Pi.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
  unfold finiteChainTraceMass finiteChainTraceExitMass filteredWordMass FilteredWordFiber
  apply tsum_congr
  intro e
  convert (tsum_subtype {w : List D | w.filter (fun a : D ↦ decide (a.val ∈ K)) = as}
    (fun w ↦ chainWordWeight P Subtype.val x w e.val)).symm using 1 <;>
      simp only [Set.indicator_apply, Set.mem_setOf_eq] <;> try rfl

end SRWTightness
