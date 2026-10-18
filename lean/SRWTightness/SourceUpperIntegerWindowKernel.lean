import SRWTightness.SourceUpperOriginalWindowNonnegative
import SRWTightness.GaussianDeficitCeilingBound
import SRWTightness.IntegerDeficitWindowIndex

namespace SRWTightness

/-- The original Gaussian summand evaluated on an integer deficit. -/
noncomputable def sourceUpperIntegerWindowKernel (t s c L : ℝ) (z : ℤ) : ℝ :=
  let d := upperTerminalDepth (sourceUpperLogRadius t)
  let x := sourceUpperTarget t s
  let S := 8 + s + 2 * d ^ (1 / 4 : ℝ)
  (S + z) / d * (1 + max (z : ℝ) 0 / Real.sqrt d) *
    Real.exp (-(x - z) ^ 2 / (2 * L) - 2 * z - c * (max (z : ℝ) 0) ^ 2 / d)

/-- Each supported chronological window is bounded by its distinct integer deficit window. -/
theorem source_upper_integer_window_comparison (t s κ L : ℝ) (i : ℕ)
    (ht : 2 ≤ t) (hκ : 0 ≤ κ)
    (hd : 1 ≤ upperTerminalDepth (sourceUpperLogRadius t)) (hL : 0 < L)
    (hi : t - 1 + (i : ℝ) ≤ sourceUpperBranchingEnd t s) :
    sourceUpperOriginalGaussianWindowKernel t s κ L (t - 1 + (i : ℝ)) ≤
      Real.exp (2 + κ / 2) * sourceUpperIntegerWindowKernel t s (κ / 4) L
        (integerDeficitWindowIndex (sourceUpperTarget t s - t + 1) i) := by
  let d := upperTerminalDepth (sourceUpperLogRadius t)
  let x := sourceUpperTarget t s
  let S := 8 + s + 2 * d ^ (1 / 4 : ℝ)
  let q := x - (t - 1 + (i : ℝ))
  let z := integerDeficitWindowIndex (x - t + 1) i
  have hq : q = x - t + 1 - (i : ℝ) := by dsimp [q]; ring
  have hz := integer_deficit_window_index_bounds (x - t + 1) i
  have hqz : q ≤ (z : ℝ) := by simpa only [hq] using hz.1
  have hzq : (z : ℝ) ≤ q + 1 := by simpa only [hq] using hz.2.le
  have hu : 1 ≤ x - q := by dsimp [q]; linarith [Nat.cast_nonneg (α := ℝ) i]
  have hS : 0 ≤ S + q := by
    dsimp [S, q, x, d, sourceUpperBranchingEnd] at *
    linarith
  exact gaussian_deficit_rounding_summand S x q z κ d L hqz hzq hu hκ hd hL hS

/-- Finite supported window sums transfer injectively to the original integer deficit lattice. -/
theorem source_upper_integer_window_sum (t s κ L : ℝ) (I : Finset ℕ)
    (ht : 2 ≤ t) (hκ : 0 ≤ κ)
    (hd : 1 ≤ upperTerminalDepth (sourceUpperLogRadius t)) (hL : 0 < L)
    (hI : ∀ i ∈ I, t - 1 + (i : ℝ) ≤ sourceUpperBranchingEnd t s) :
    (∑ i ∈ I, sourceUpperOriginalGaussianWindowKernel t s κ L (t - 1 + (i : ℝ))) ≤
      Real.exp (2 + κ / 2) *
        ∑ z ∈ I.image (integerDeficitWindowIndex (sourceUpperTarget t s - t + 1)),
          sourceUpperIntegerWindowKernel t s (κ / 4) L z := by
  classical
  rw [Finset.sum_image]
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i hi ↦
      source_upper_integer_window_comparison t s κ L i ht hκ hd hL (hI i hi))
  · intro i hi j hj hij
    exact integer_deficit_window_index_injective _ hij

end SRWTightness
