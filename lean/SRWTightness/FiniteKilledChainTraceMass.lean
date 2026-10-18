import SRWTightness.FilteredWordFactorization

open scoped ENNReal

namespace SRWTightness

/-- The full finite-path exit mass for an arbitrary transition matrix killed outside a domain. -/
noncomputable def finiteChainExitMass {σ : Type*} (P : σ → σ → ℝ≥0∞)
    (D : Set σ) (x e : σ) : ℝ≥0∞ :=
  ∑' w : List D, chainWordWeight P Subtype.val x w e

/-- The joint finite-path mass of the ordered post-initial trace and prescribed exit. -/
noncomputable def finiteChainTraceExitMass {σ : Type*} (P : σ → σ → ℝ≥0∞)
    (D K : Set σ) [DecidablePred (· ∈ K)] (x e : σ) (as : List D) : ℝ≥0∞ :=
  filteredWordMass P Subtype.val (fun a : D ↦ decide (a.val ∈ K)) x e as

/-- The finite trace mass sums over every terminal state outside the killing domain. -/
noncomputable def finiteChainTraceMass {σ : Type*} (P : σ → σ → ℝ≥0∞)
    (D K : Set σ) [DecidablePred (· ∈ K)] (x : σ) (as : List D) : ℝ≥0∞ :=
  ∑' e : {y : σ // y ∉ D}, finiteChainTraceExitMass P D K x e.val as

/-- First-return products factor the actual joint and marginal finite-path trace masses. -/
theorem finiteChain_trace_common_factor {σ : Type*} (P : σ → σ → ℝ≥0∞)
    (D K : Set σ) [DecidablePred (· ∈ K)] (x e : σ) (as : List D)
    (ha : ∀ a ∈ as, a.val ∈ K) :
    ∃ w : ℝ≥0∞,
      finiteChainTraceExitMass P D K x e as =
        w * finiteChainTraceExitMass P D K (as.foldl (fun _ a ↦ a.val) x) e [] ∧
      finiteChainTraceMass P D K x as =
        w * finiteChainTraceMass P D K (as.foldl (fun _ a ↦ a.val) x) [] := by
  let p := fun a : D ↦ decide (a.val ∈ K)
  have hp : ∀ a ∈ as, p a := by simpa only [p, decide_eq_true_eq] using ha
  refine ⟨filteredReturnWeight P Subtype.val p x as, ?_, ?_⟩
  · exact filteredWordMass_factorization P Subtype.val p x e as hp
  · exact filteredWordMass_exit_sum_factorization P Subtype.val p x
      (fun e : {y : σ // y ∉ D} ↦ e.val) as hp

end SRWTightness
