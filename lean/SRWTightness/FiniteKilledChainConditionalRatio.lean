import SRWTightness.FiniteKilledChainTraceLaw
import SRWTightness.FiniteKilledChainTraceRatio
import SRWTightness.FiniteKilledChainFullTrace
import Mathlib.MeasureTheory.Measure.Real

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

attribute [local instance] finiteChainListMeasurableSpace finiteChainListMeasurableSingleton

/-- The literal complete-trace conditional ratio for an arbitrary countable substochastic chain. -/
theorem finite_killed_chain_trace_conditional_ratio {σ : Type*} [MeasurableSpace σ]
    [MeasurableSingletonClass σ] [Countable σ]
    (P : σ → σ → ℝ≥0∞) (D K : Set σ) [DecidablePred (· ∈ K)]
    (hP : ∀ x, ∑' y, P x y ≤ 1) (x : σ) (hx : x ∈ K)
    (e : {y : σ // y ∉ D}) (as : List D)
    (hp : 0 < (finiteChainKilledWordLaw P D x).real
      {q | finiteChainFullTrace D K x q = x :: as.map Subtype.val})
    (he : 0 < (finiteChainKilledWordLaw P D x).real {q | q.2 = e}) :
    (((finiteChainKilledWordLaw P D x).real
        {q | finiteChainFullTrace D K x q = x :: as.map Subtype.val ∧ q.2 = e}) /
      (finiteChainKilledWordLaw P D x).real {q | q.2 = e}) /
      (finiteChainKilledWordLaw P D x).real
        {q | finiteChainFullTrace D K x q = x :: as.map Subtype.val} =
    (finiteChainKilledWordLaw P D (as.foldl (fun _ a ↦ a.val) x)).real
        {q | q.1.filter (fun a : D ↦ decide (a.val ∈ K)) = [] ∧ q.2 = e} /
      ((finiteChainKilledWordLaw P D x).real {q | q.2 = e} *
        (finiteChainKilledWordLaw P D (as.foldl (fun _ a ↦ a.val) x)).real
          {q | q.1.filter (fun a : D ↦ decide (a.val ∈ K)) = []}) := by
  have ha : ∀ a ∈ as, a.val ∈ K := by
    obtain ⟨q, hq⟩ := nonempty_of_measureReal_ne_zero hp.ne'
    have ht := (finiteChainFullTrace_eq_iff D K x hx q as).mp hq
    intro a ha
    rw [← ht] at ha
    exact of_decide_eq_true (List.mem_filter.mp ha).2
  simp only [finiteChainFullTrace_eq_iff D K x hx] at hp ⊢
  simp only [Measure.real, finiteChainKilledWordLaw_trace,
    finiteChainKilledWordLaw_trace_exit, finiteChainKilledWordLaw_exit] at hp he ⊢
  exact finiteChain_trace_conditional_ratio_mass P D K x e.val as ha hp he

end SRWTightness
