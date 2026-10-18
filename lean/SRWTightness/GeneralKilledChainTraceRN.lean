import SRWTightness.FiniteKilledChainConditionalRatio
import SRWTightness.FiniteChainLastSite

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

attribute [local instance] finiteChainListMeasurableSpace finiteChainListMeasurableSingleton

/-- The manuscript trace Radon--Nikodym ratio for every positive complete trace of a
killed chain. -/
theorem general_killed_chain_trace_rn {σ : Type*} [MeasurableSpace σ]
    [MeasurableSingletonClass σ] [Countable σ]
    (P : σ → σ → ℝ≥0∞) (D K : Set σ) [DecidablePred (· ∈ K)]
    (hP : ∀ x, ∑' y, P x y ≤ 1) (hKD : K ⊆ D) (x : σ) (hx : x ∈ K)
    (e : {y : σ // y ∉ D}) (ξ : List σ)
    (hξ : 0 < (finiteChainKilledWordLaw P D x).real
      {q | finiteChainFullTrace D K x q = ξ})
    (he : 0 < (finiteChainKilledWordLaw P D x).real {q | q.2 = e}) :
    (((finiteChainKilledWordLaw P D x).real
        {q | finiteChainFullTrace D K x q = ξ ∧ q.2 = e}) /
      (finiteChainKilledWordLaw P D x).real {q | q.2 = e}) /
      (finiteChainKilledWordLaw P D x).real {q | finiteChainFullTrace D K x q = ξ} =
    (finiteChainKilledWordLaw P D (ξ.getLastD x)).real
        {q | q.1.filter (fun a : D ↦ decide (a.val ∈ K)) = [] ∧ q.2 = e} /
      ((finiteChainKilledWordLaw P D x).real {q | q.2 = e} *
        (finiteChainKilledWordLaw P D (ξ.getLastD x)).real
          {q | q.1.filter (fun a : D ↦ decide (a.val ∈ K)) = []}) := by
  obtain ⟨q, hq⟩ := nonempty_of_measureReal_ne_zero hξ.ne'
  let as := q.1.filter (fun a : D ↦ decide (a.val ∈ K))
  have hrep : ξ = x :: as.map Subtype.val :=
    hq.symm.trans ((finiteChainFullTrace_eq_iff D K x hx q as).mpr rfl)
  have hz : as.foldl (fun _ a ↦ a.val) x = ξ.getLastD x := by
    rw [hrep]
    exact finiteChain_fold_last_site Subtype.val x as
  have hp : 0 < (finiteChainKilledWordLaw P D x).real
      {q | finiteChainFullTrace D K x q = x :: as.map Subtype.val} := by
    rwa [← hrep]
  have hh := finite_killed_chain_trace_conditional_ratio P D K hP x hx e as hp he
  simpa only [← hrep, hz] using hh

end SRWTightness
