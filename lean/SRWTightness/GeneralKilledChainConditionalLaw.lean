import SRWTightness.GeneralKilledChainTraceRN
import Mathlib.Probability.ConditionalProbability

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SRWTightness

attribute [local instance] finiteChainListMeasurableSpace finiteChainListMeasurableSingleton

/-- The trace ratio uses the actual conditional measure given the prescribed exit atom. -/
theorem general_killed_chain_conditional_trace_law {σ : Type*} [MeasurableSpace σ]
    [MeasurableSingletonClass σ] [Countable σ]
    (P : σ → σ → ℝ≥0∞) (D K : Set σ) [DecidablePred (· ∈ K)]
    (hP : ∀ x, ∑' y, P x y ≤ 1) (hKD : K ⊆ D) (x : σ) (hx : x ∈ K)
    (e : {y : σ // y ∉ D}) (ξ : List σ)
    (hξ : 0 < (finiteChainKilledWordLaw P D x).real
      {q | finiteChainFullTrace D K x q = ξ})
    (he : 0 < (finiteChainKilledWordLaw P D x).real {q | q.2 = e}) :
    (cond (finiteChainKilledWordLaw P D x) {q | q.2 = e}).real
        {q | finiteChainFullTrace D K x q = ξ} /
      (finiteChainKilledWordLaw P D x).real {q | finiteChainFullTrace D K x q = ξ} =
    (finiteChainKilledWordLaw P D (ξ.getLastD x)).real
        {q | q.1.filter (fun a : D ↦ decide (a.val ∈ K)) = [] ∧ q.2 = e} /
      ((finiteChainKilledWordLaw P D x).real {q | q.2 = e} *
        (finiteChainKilledWordLaw P D (ξ.getLastD x)).real
          {q | q.1.filter (fun a : D ↦ decide (a.val ∈ K)) = []}) := by
  have hc : (cond (finiteChainKilledWordLaw P D x) {q | q.2 = e}).real
        {q | finiteChainFullTrace D K x q = ξ} =
      (finiteChainKilledWordLaw P D x).real
          {q | finiteChainFullTrace D K x q = ξ ∧ q.2 = e} /
        (finiteChainKilledWordLaw P D x).real {q | q.2 = e} := by
    have hi : {q : List D × {y : σ // y ∉ D} | q.2 = e} ∩
        {q | finiteChainFullTrace D K x q = ξ} =
        {q | finiteChainFullTrace D K x q = ξ ∧ q.2 = e} := by
      ext q
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, and_comm]
    simp only [Measure.real, cond_apply (Set.to_countable _).measurableSet,
      ENNReal.toReal_mul, ENNReal.toReal_inv, hi, div_eq_mul_inv, mul_comm]
  rw [hc]
  exact general_killed_chain_trace_rn P D K hP hKD x hx e ξ hξ he

end SRWTightness
