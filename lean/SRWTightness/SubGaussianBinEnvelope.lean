import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace SRWTightness

/-- The positive exponential moment at the upper endpoint of a unit interval. -/
noncomputable def subGaussianBinWeight (b : ℝ) (n : ℕ) : ℝ :=
  Real.exp (2 * ((n : ℝ) + 1) + b / 2 * ((n : ℝ) + 1) ^ 2)

/-- The completion-of-square constant for a geometrically summable bin envelope. -/
noncomputable def subGaussianBinConstant (b : ℝ) : ℝ :=
  b / 2 + 2 + (5 * b / 4 + 2) ^ 2 / (2 * b)

/-- A uniform summable envelope for the bin weight times a sub-Gaussian tail. -/
noncomputable def subGaussianBinBound (A b : ℝ) (n : ℕ) : ℝ :=
  A * Real.exp (subGaussianBinConstant b) * (Real.exp (-b / 4)) ^ n

/-- Completing the square absorbs every bin's growing moment weight into a geometric tail. -/
theorem sub_gaussian_bin_weight_envelope (A b : ℝ) (hA : 0 < A) (hb : 0 < b) (n : ℕ) :
    subGaussianBinWeight b n * (A * Real.exp (-b * (n : ℝ) ^ 2)) ≤
      subGaussianBinBound A b n := by
  have he : 2 * ((n : ℝ) + 1) + b / 2 * ((n : ℝ) + 1) ^ 2 - b * (n : ℝ) ^ 2 =
      subGaussianBinConstant b - b / 4 * (n : ℝ) -
        b / 2 * ((n : ℝ) - (5 * b / 4 + 2) / b) ^ 2 := by
    unfold subGaussianBinConstant
    field_simp [hb.ne'] <;> ring
  have hc : 2 * ((n : ℝ) + 1) + b / 2 * ((n : ℝ) + 1) ^ 2 - b * (n : ℝ) ^ 2 ≤
      subGaussianBinConstant b - b / 4 * (n : ℝ) := by
    rw [he]
    exact sub_le_self _ (mul_nonneg (by positivity) (sq_nonneg _))
  have hp : (Real.exp (-b / 4)) ^ n = Real.exp (-(b / 4) * (n : ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  calc
    _ = A * Real.exp
        (2 * ((n : ℝ) + 1) + b / 2 * ((n : ℝ) + 1) ^ 2 - b * (n : ℝ) ^ 2) := by
      simp only [subGaussianBinWeight, sub_eq_add_neg, Real.exp_add, neg_mul]
      ring
    _ ≤ A * Real.exp (subGaussianBinConstant b - b / 4 * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hc) hA.le
    _ = subGaussianBinBound A b n := by
      unfold subGaussianBinBound
      rw [hp, mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- The uniform bin envelope is summable for every strictly positive sub-Gaussian rate. -/
theorem sub_gaussian_bin_bound_summable (A b : ℝ) (hb : 0 < b) :
    Summable (subGaussianBinBound A b) := by
  have hρ : ‖Real.exp (-b / 4)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  change Summable (fun n : ℕ ↦
    A * Real.exp (subGaussianBinConstant b) * (Real.exp (-b / 4)) ^ n)
  exact (summable_geometric_of_norm_lt_one hρ).mul_left (A * Real.exp (subGaussianBinConstant b))

end SRWTightness
