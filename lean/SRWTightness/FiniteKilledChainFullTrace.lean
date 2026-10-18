import SRWTightness.FiniteKilledChainWordLaw

namespace SRWTightness

/-- All visits to the marked set before killing, including the initial site when marked. -/
def finiteChainFullTrace {σ : Type*} (D K : Set σ) [DecidablePred (· ∈ K)]
    (x : σ) (q : List D × {y : σ // y ∉ D}) : List σ :=
  (x :: q.1.map Subtype.val).filter (fun y ↦ decide (y ∈ K))

/-- With a marked starting site, the complete trace is exactly its start and filtered
interior word. -/
theorem finiteChainFullTrace_eq_iff {σ : Type*} (D K : Set σ) [DecidablePred (· ∈ K)]
    (x : σ) (hx : x ∈ K) (q : List D × {y : σ // y ∉ D}) (as : List D) :
    finiteChainFullTrace D K x q = x :: as.map Subtype.val ↔
      q.1.filter (fun a : D ↦ decide (a.val ∈ K)) = as := by
  simp only [finiteChainFullTrace, List.filter_cons, hx, decide_true, ↓reduceIte,
    List.filter_map, List.cons.injEq, true_and]
  exact List.map_inj_right Subtype.val_injective

end SRWTightness
