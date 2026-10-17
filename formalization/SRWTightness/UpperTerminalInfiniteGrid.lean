import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

namespace SRWTightness

/-- Uniform bounds on descending finite grids control every nonnegative ascending lattice ray. -/
theorem upper_terminal_infinite_grid (f : ℝ → ℝ) (a C : ℝ)
    (hf : ∀ q : ℝ, a ≤ q → 0 ≤ f q)
    (hbound : ∀ v : ℝ, ∀ I : Finset ℕ, (∀ J ∈ I, a ≤ v - (J : ℝ)) →
      (∑ J ∈ I, f (v - (J : ℝ))) ≤ C) (w : ℝ) (hw : a ≤ w) :
    Summable (fun n : ℕ ↦ f (w + (n : ℝ))) ∧
      (∑' n : ℕ, f (w + (n : ℝ))) ≤ C := by
  have hnonneg (n : ℕ) : 0 ≤ f (w + (n : ℝ)) := hf _ (by
    linarith [Nat.cast_nonneg (α := ℝ) n])
  have hpartial (n : ℕ) : (∑ J ∈ Finset.range n, f (w + (J : ℝ))) ≤ C := by
    have hJ (J : ℕ) (hJ : J ∈ Finset.range n) : J ≤ n - 1 := by
      have hh := Finset.mem_range.mp hJ
      omega
    have he (J : ℕ) (hj : J ∈ Finset.range n) :
        w + ((n - 1 - J : ℕ) : ℝ) = (w + ((n - 1 : ℕ) : ℝ)) - (J : ℝ) := by
      rw [Nat.cast_sub (hJ J hj)]
      ring
    calc
      _ = ∑ J ∈ Finset.range n, f (w + ((n - 1 - J : ℕ) : ℝ)) :=
        (Finset.sum_range_reflect (fun J : ℕ ↦ f (w + (J : ℝ))) n).symm
      _ = ∑ J ∈ Finset.range n, f ((w + ((n - 1 : ℕ) : ℝ)) - (J : ℝ)) :=
        Finset.sum_congr rfl (fun J hj ↦ congrArg f (he J hj))
      _ ≤ C := hbound _ _ (fun J hj ↦ by
        rw [← he J hj]
        linarith [Nat.cast_nonneg (α := ℝ) (n - 1 - J)])
  exact ⟨summable_of_sum_range_le hnonneg hpartial,
    Real.tsum_le_of_sum_range_le hnonneg hpartial⟩

end SRWTightness
