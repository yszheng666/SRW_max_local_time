import SRWTightness.FiniteKilledChainTraceMass
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open scoped ENNReal

namespace SRWTightness

/-- The general finite-path trace ratio cancels the proved common first-return product. -/
theorem finiteChain_trace_conditional_ratio_mass {σ : Type*}
    (P : σ → σ → ℝ≥0∞) (D K : Set σ) [DecidablePred (· ∈ K)]
    (x e : σ) (as : List D) (ha : ∀ a ∈ as, a.val ∈ K)
    (hp : 0 < (finiteChainTraceMass P D K x as).toReal)
    (he : 0 < (finiteChainExitMass P D x e).toReal) :
    ((finiteChainTraceExitMass P D K x e as).toReal /
        (finiteChainExitMass P D x e).toReal) / (finiteChainTraceMass P D K x as).toReal =
      (finiteChainTraceExitMass P D K (as.foldl (fun _ a ↦ a.val) x) e []).toReal /
        ((finiteChainExitMass P D x e).toReal *
          (finiteChainTraceMass P D K (as.foldl (fun _ a ↦ a.val) x) []).toReal) := by
  obtain ⟨w, hj, ht⟩ := finiteChain_trace_common_factor P D K x e as ha
  have hprod : w.toReal *
      (finiteChainTraceMass P D K (as.foldl (fun _ a ↦ a.val) x) []).toReal ≠ 0 := by
    rw [← ENNReal.toReal_mul, ← ht]
    exact hp.ne'
  have hw := (mul_ne_zero_iff.mp hprod).1
  have hq := (mul_ne_zero_iff.mp hprod).2
  rw [hj, ht, ENNReal.toReal_mul, ENNReal.toReal_mul]
  field_simp
  <;> ring

end SRWTightness
