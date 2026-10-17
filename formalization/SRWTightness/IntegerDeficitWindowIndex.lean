import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

namespace SRWTightness

/-- Round the actual unit-spaced deficit window upward onto the original integer lattice. -/
noncomputable def integerDeficitWindowIndex (a : ℝ) (i : ℕ) : ℤ := ⌈a - i⌉

/-- The integer deficit index is its fixed origin minus the original window number. -/
theorem integer_deficit_window_index_eq (a : ℝ) (i : ℕ) :
    integerDeficitWindowIndex a i = ⌈a⌉ - (i : ℤ) := Int.ceil_sub_natCast a i

/-- Distinct chronological unit windows remain distinct after integer deficit rounding. -/
theorem integer_deficit_window_index_injective (a : ℝ) :
    Function.Injective (integerDeficitWindowIndex a) := by
  intro i j hij
  rw [integer_deficit_window_index_eq, integer_deficit_window_index_eq] at hij
  have hc : (i : ℤ) = j := by omega
  exact_mod_cast hc

/-- Integer rounding is upward and shifts a unit window by less than one. -/
theorem integer_deficit_window_index_bounds (a : ℝ) (i : ℕ) :
    a - i ≤ (integerDeficitWindowIndex a i : ℝ) ∧
      (integerDeficitWindowIndex a i : ℝ) < a - i + 1 :=
  ⟨Int.le_ceil _, Int.ceil_lt_add_one _⟩

end SRWTightness
