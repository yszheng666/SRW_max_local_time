import SRWTightness.GaussianSeriesContinuity
import Mathlib.Tactic.FieldSimp

namespace SRWTightness

theorem schauderTent_nat_difference (j k : ℕ) : schauderTent ((j : ℝ) - k) = 0 := by
  by_cases h : j ≤ k
  · apply schauderTent_eq_zero_left
    exact sub_nonpos.mpr (by exact_mod_cast h)
  · apply schauderTent_eq_zero_right
    have hn : k + 1 ≤ j := Nat.lt_of_not_ge h
    have hr : (k : ℝ) + 1 ≤ j := by exact_mod_cast hn
    linarith

theorem schauderLevel_dyadic_zero (m n j : ℕ) (hmn : m ≤ n) (c : ℝ) (z : ℕ → ℝ) :
    schauderLevel (2 ^ n) ((2 : ℝ) ^ n) c z ((j : ℝ) / (2 : ℝ) ^ m) = 0 := by
  have hp : (2 : ℝ) ^ n = (2 : ℝ) ^ (n - m) * (2 : ℝ) ^ m := by
    rw [← pow_add, Nat.sub_add_cancel hmn]
  have ht : (2 : ℝ) ^ n * ((j : ℝ) / (2 : ℝ) ^ m) = (j * 2 ^ (n - m) : ℕ) := by
    push_cast
    rw [hp]
    field_simp
  apply Finset.sum_eq_zero
  intro k hk
  simp only [scaledSchauderTent, ht, schauderTent_nat_difference, mul_zero]

/-- At dyadic times the infinite series is exactly a finite Gaussian expression. -/
theorem gaussianDyadicPath_dyadic (ω : GaussianCoefficientSpace) (m j : ℕ) :
    gaussianDyadicPath ω ((j : ℝ) / (2 : ℝ) ^ m) =
      ((j : ℝ) / (2 : ℝ) ^ m) * ω none +
      ∑ n ∈ Finset.range m, schauderLevel (2 ^ n) ((2 : ℝ) ^ n)
        ((Real.sqrt 2)⁻¹ ^ n) (fun k ↦ ω (some (n, k))) ((j : ℝ) / (2 : ℝ) ^ m) := by
  unfold gaussianDyadicPath
  congr 1
  apply tsum_eq_sum
  intro n hn
  exact schauderLevel_dyadic_zero m n j (Nat.le_of_not_gt (by simpa using hn)) _ _

end SRWTightness
