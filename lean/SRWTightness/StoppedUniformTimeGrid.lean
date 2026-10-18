import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

namespace SRWTightness

/-- A finite uniform time grid, held constant at its final endpoint afterward. -/
noncomputable def stoppedUniformTimeGrid (a b : ℝ) (N n : ℕ) : ℝ :=
  a + (b - a) * (min n N : ℕ) / N

/-- The stopped uniform grid begins exactly at its first endpoint. -/
theorem stoppedUniformTimeGrid_zero (a b : ℝ) (N : ℕ) :
    stoppedUniformTimeGrid a b N 0 = a := by simp [stoppedUniformTimeGrid]

/-- The stopped uniform grid is nondecreasing. -/
theorem stoppedUniformTimeGrid_mono (a b : ℝ) (N : ℕ) (hab : a ≤ b) :
    Monotone (stoppedUniformTimeGrid a b N) := by
  intro n m hnm
  unfold stoppedUniformTimeGrid
  apply add_le_add le_rfl
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hab)
  exact_mod_cast min_le_min_right N hnm

/-- Every point of a nonempty stopped uniform grid lies between its endpoints. -/
theorem stoppedUniformTimeGrid_mem (a b : ℝ) (N n : ℕ) (hab : a ≤ b) (hN : 0 < N) :
    stoppedUniformTimeGrid a b N n ∈ Set.Icc a b := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hmin : ((min n N : ℕ) : ℝ) ≤ N := by exact_mod_cast min_le_right n N
  unfold stoppedUniformTimeGrid
  constructor
  · have h : 0 ≤ (b - a) * (min n N : ℕ) / (N : ℝ) := by positivity
    linarith
  · have h := mul_le_mul_of_nonneg_left hmin (sub_nonneg.mpr hab)
    have hd : (b - a) * (min n N : ℕ) / (N : ℝ) ≤ b - a :=
      (div_le_iff₀ hNr).mpr h
    linarith

/-- Before its endpoint, the grid agrees with the literal uniform subdivision. -/
theorem stoppedUniformTimeGrid_of_le (a b : ℝ) (N n : ℕ) (hn : n ≤ N) :
    stoppedUniformTimeGrid a b N n = a + (b - a) * n / N := by
  simp only [stoppedUniformTimeGrid, min_eq_left hn]

end SRWTightness
