import SRWTightness.SchauderTent
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped BigOperators

namespace SRWTightness

/-- A finite level of equally spaced tents with arbitrary real coefficients. -/
noncomputable def schauderLevel (N : ℕ) (a c : ℝ) (z : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, z k * scaledSchauderTent a k c t

theorem schauderLevel_continuous (N : ℕ) (a c : ℝ) (z : ℕ → ℝ) :
    Continuous (schauderLevel N a c z) := by
  unfold schauderLevel
  exact continuous_finsetSum _ (fun k _ ↦
    continuous_const.mul (scaledSchauderTent_continuous a k c))

theorem schauderLevel_bound (N : ℕ) (a c M t : ℝ) (z : ℕ → ℝ)
    (hc : 0 ≤ c) (hM : 0 ≤ M) (hz : ∀ k < N, |z k| ≤ M) :
    |schauderLevel N a c z t| ≤ M * c / 2 := by
  classical
  by_cases he : ∃ k ∈ Finset.range N, 0 < schauderTent (a * t - k)
  · obtain ⟨k, hk, hpos⟩ := he
    have hs : schauderLevel N a c z t = z k * scaledSchauderTent a k c t := by
      apply Finset.sum_eq_single k
      · intro l hl hlk
        have hzero := schauderTent_translate_disjoint (a * t) k l (Ne.symm hlk) hpos
        simp [scaledSchauderTent, hzero]
      · exact fun h ↦ (h hk).elim
    rw [hs, abs_mul, abs_of_nonneg (scaledSchauderTent_bounds a k c t hc).1]
    have h := mul_le_mul (hz k (Finset.mem_range.mp hk))
      (scaledSchauderTent_bounds a k c t hc).2
      (scaledSchauderTent_bounds a k c t hc).1 hM
    simpa [mul_div_assoc] using h
  · have hs : schauderLevel N a c z t = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      have hzero : schauderTent (a * t - k) = 0 :=
        le_antisymm (le_of_not_gt (fun h ↦ he ⟨k, hk, h⟩)) (schauderTent_nonneg _)
      simp [scaledSchauderTent, hzero]
    rw [hs, abs_zero]
    positivity

/-- Summable bounds on the levels give a continuous real path. -/
theorem schauderSeries_continuous (N : ℕ → ℕ) (a c M : ℕ → ℝ)
    (z : ℕ → ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hM : ∀ n, 0 ≤ M n)
    (hz : ∀ n k, k < N n → |z n k| ≤ M n)
    (hs : Summable (fun n ↦ M n * c n / 2)) :
    Continuous (fun t ↦ ∑' n, schauderLevel (N n) (a n) (c n) (z n) t) := by
  apply continuous_tsum (fun n ↦ schauderLevel_continuous _ _ _ _) hs
  intro n t
  simpa only [Real.norm_eq_abs] using
    schauderLevel_bound (N n) (a n) (c n) (M n) t (z n) (hc n) (hM n) (hz n)

end SRWTightness
