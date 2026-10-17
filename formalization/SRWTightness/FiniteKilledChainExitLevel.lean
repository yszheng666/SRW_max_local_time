import SRWTightness.FiniteKilledChainTraceMass
import Mathlib.Logic.Equiv.Set
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open scoped ENNReal BigOperators

namespace SRWTightness

/-- Exit mass after exactly the indicated number of intermediate in-domain sites. -/
noncomputable def finiteChainExitLevel {σ : Type*} (P : σ → σ → ℝ≥0∞) (D : Set σ) :
    ℕ → σ → ℝ≥0∞
  | 0, x => ∑' e : {y : σ // y ∉ D}, P x e.val
  | n + 1, x => ∑' a : D, P x a.val * finiteChainExitLevel P D n a.val

/-- Splitting one transition by whether its endpoint stays in the domain preserves its mass. -/
theorem finiteChain_row_split {σ : Type*} (P : σ → σ → ℝ≥0∞) (D : Set σ) (x : σ) :
    (∑' a : D, P x a.val) + (∑' e : {y : σ // y ∉ D}, P x e.val) = ∑' y, P x y := by
  classical
  calc
    _ = ∑' z : D ⊕ {y : σ // y ∉ D}, P x ((Equiv.Set.sumCompl D) z) :=
      (ENNReal.summable.tsum_sum ENNReal.summable).symm
    _ = _ := (Equiv.Set.sumCompl D).tsum_eq _

/-- A substochastic transition matrix assigns at most unit mass to all finite exit times. -/
theorem finiteChain_exit_levels_le_one {σ : Type*} (P : σ → σ → ℝ≥0∞) (D : Set σ)
    (hP : ∀ x, ∑' y, P x y ≤ 1) (x : σ) :
    (∑' n : ℕ, finiteChainExitLevel P D n x) ≤ 1 := by
  have hb (N : ℕ) : ∀ x, (∑ n ∈ Finset.range N, finiteChainExitLevel P D n x) ≤ 1 := by
    induction N with
    | zero => intro x; simp
    | succ N ih =>
        intro x
        rw [Finset.sum_range_succ']
        simp only [finiteChainExitLevel]
        rw [← Summable.tsum_finsetSum (fun _ _ ↦ ENNReal.summable)]
        simp only [← Finset.mul_sum]
        calc
          _ ≤ (∑' a : D, P x a.val) + (∑' e : {y : σ // y ∉ D}, P x e.val) := by
            refine add_le_add ?_ le_rfl
            apply ENNReal.tsum_le_tsum
            intro a
            simpa using mul_le_mul_left' (ih a.val) (P x a.val)
          _ = ∑' y, P x y := finiteChain_row_split P D x
          _ ≤ 1 := hP x
  exact ENNReal.tsum_le_of_sum_range_le (fun N ↦ hb N x)

end SRWTightness
