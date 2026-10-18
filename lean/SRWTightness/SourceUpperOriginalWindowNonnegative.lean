import SRWTightness.SourceUpperOriginalWindowSum

namespace SRWTightness

/-- The original Gaussian kernel is nonnegative on every actual supported terminal window. -/
theorem source_upper_original_window_kernel_nonneg (t s κ L u : ℝ)
    (hd : 0 ≤ upperTerminalDepth (sourceUpperLogRadius t))
    (hu : u ≤ sourceUpperBranchingEnd t s) :
    0 ≤ sourceUpperOriginalGaussianWindowKernel t s κ L u := by
  have hslack : 0 ≤ sourceUpperBranchingSlack t s u := by
    unfold sourceUpperBranchingSlack
    linarith
  have hS : 0 ≤ 8 + s + 2 * upperTerminalDepth (sourceUpperLogRadius t) ^ (1 / 4 : ℝ) +
      (sourceUpperTarget t s - u) := by
    dsimp [sourceUpperBranchingSlack, sourceUpperBranchingEnd, sourceUpperTarget] at hslack ⊢
    linarith
  unfold sourceUpperOriginalGaussianWindowKernel
  exact mul_nonneg (mul_nonneg (div_nonneg hS hd) (by positivity)) (Real.exp_nonneg _)

end SRWTightness
