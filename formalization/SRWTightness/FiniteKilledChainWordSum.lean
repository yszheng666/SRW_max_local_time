import SRWTightness.FiniteKilledChainExitLevel
import Mathlib.Data.List.OfFn

open scoped ENNReal

namespace SRWTightness

/-- A finite sequence splits into its first site and its remaining coordinates. -/
def finiteChainTupleConsEquiv (α : Type*) (n : ℕ) :
    (α × (Fin n → α)) ≃ (Fin (n + 1) → α) where
  toFun q := Fin.cons q.1 q.2
  invFun v := (v 0, fun i ↦ v i.succ)
  left_inv q := by simp
  right_inv v := by funext i; exact Fin.cases rfl (fun _ ↦ rfl) i

/-- The recursively summed exit level is exactly the sum of all corresponding finite paths. -/
theorem finiteChainExitLevel_word_sum {σ : Type*} (P : σ → σ → ℝ≥0∞) (D : Set σ)
    (n : ℕ) (x : σ) :
    finiteChainExitLevel P D n x = ∑' v : Fin n → D,
      ∑' e : {y : σ // y ∉ D}, chainWordWeight P Subtype.val x (List.ofFn v) e.val := by
  induction n generalizing x with
  | zero => simp [finiteChainExitLevel, chainWordWeight]
  | succ n ih =>
      rw [← (finiteChainTupleConsEquiv D n).tsum_eq]
      change finiteChainExitLevel P D (n + 1) x =
        ∑' q : D × (Fin n → D), ∑' e : {y : σ // y ∉ D},
          chainWordWeight P Subtype.val x (List.ofFn (Fin.cons q.1 q.2)) e.val
      simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, chainWordWeight]
      rw [ENNReal.tsum_prod']
      simp only [ENNReal.tsum_mul_left, finiteChainExitLevel, ih]

/-- Summing all complete finite paths agrees with summing the mutually exclusive exit lengths. -/
theorem finiteChainExitMass_sum_eq_levels {σ : Type*} (P : σ → σ → ℝ≥0∞)
    (D : Set σ) (x : σ) :
    (∑' e : {y : σ // y ∉ D}, finiteChainExitMass P D x e.val) =
      ∑' n : ℕ, finiteChainExitLevel P D n x := by
  unfold finiteChainExitMass
  rw [ENNReal.tsum_comm]
  rw [← (List.equivSigmaTuple (α := D)).symm.tsum_eq]
  rw [ENNReal.tsum_sigma']
  apply tsum_congr
  intro n
  exact (finiteChainExitLevel_word_sum P D n x).symm

/-- All complete killed paths of a substochastic chain have total mass at most one. -/
theorem finiteChainExitMass_sum_le_one {σ : Type*} (P : σ → σ → ℝ≥0∞)
    (D : Set σ) (hP : ∀ x, ∑' y, P x y ≤ 1) (x : σ) :
    (∑' e : {y : σ // y ∉ D}, finiteChainExitMass P D x e.val) ≤ 1 := by
  rw [finiteChainExitMass_sum_eq_levels]
  exact finiteChain_exit_levels_le_one P D hP x

end SRWTightness
