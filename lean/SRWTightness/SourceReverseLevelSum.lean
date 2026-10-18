import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators
namespace SRWTightness

/-- Remaining-depth sums equal the manuscript's forward sums between the root and terminal level. -/
theorem source_reverse_level_sum (ℓ k : ℕ) (hk : k < ℓ) (f : ℕ → ℝ) :
    (∑ i ∈ Finset.range (ℓ - (k + 1)), f i) =
      ∑ j ∈ Finset.Icc (k + 1) (ℓ - 1), f (ℓ - (j + 1)) := by
  apply Finset.sum_bij (fun i _ ↦ ℓ - (i + 1))
  · intro i hi
    simp only [Finset.mem_range] at hi
    simp only [Finset.mem_Icc]
    omega
  · intro i hi j hj he
    simp only [Finset.mem_range] at hi hj
    omega
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    refine ⟨ℓ - (j + 1), ?_, ?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro i hi
    simp only [Finset.mem_range] at hi
    congr 1
    omega

end SRWTightness
