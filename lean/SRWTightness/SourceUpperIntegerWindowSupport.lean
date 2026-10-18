import SRWTightness.SourceUpperIntegerWindowKernel
import SRWTightness.SourceUpperSupportedPrincipalReal

namespace SRWTightness

/-- Integer deficits above the manuscript cutoff have nonnegative Gaussian summands. -/
theorem source_upper_integer_window_kernel_nonneg (t s c L : ℝ) (z : ℤ)
    (hd : 0 ≤ upperTerminalDepth (sourceUpperLogRadius t))
    (hz : -(7 + s + upperTerminalDepth (sourceUpperLogRadius t) ^ (1 / 4 : ℝ)) ≤
      (z : ℝ)) : 0 ≤ sourceUpperIntegerWindowKernel t s c L z := by
  have hr := Real.rpow_nonneg hd (1 / 4 : ℝ)
  have hS : 0 ≤ 8 + s + 2 * upperTerminalDepth (sourceUpperLogRadius t) ^
      (1 / 4 : ℝ) + (z : ℝ) := by linarith
  unfold sourceUpperIntegerWindowKernel
  exact mul_nonneg (mul_nonneg (div_nonneg hS hd) (by positivity)) (Real.exp_nonneg _)

/-- Rounding the actual supported windows preserves the manuscript deficit cutoff. -/
theorem source_upper_integer_supported_window_cutoff (t s : ℝ) (i : ℕ)
    (hi : i ∈ sourceUpperSupportedWindowIndices t s) :
    -(7 + s + upperTerminalDepth (sourceUpperLogRadius t) ^ (1 / 4 : ℝ)) ≤
      (integerDeficitWindowIndex (sourceUpperTarget t s - t + 1) i : ℝ) := by
  have hq := (Finset.mem_filter.mp hi).2.1
  have hz := (integer_deficit_window_index_bounds (sourceUpperTarget t s - t + 1) i).1
  linarith

/-- The actual supported finite principal windows transfer to distinct admissible integers. -/
theorem source_upper_integer_supported_window_sum (t s κ L : ℝ)
    (ht : 2 ≤ t) (hκ : 0 ≤ κ)
    (hd : 1 ≤ upperTerminalDepth (sourceUpperLogRadius t)) (hL : 0 < L) :
    (∑ i ∈ sourceUpperSupportedWindowIndices t s,
      sourceUpperOriginalGaussianWindowKernel t s κ L (t - 1 + (i : ℝ))) ≤
      Real.exp (2 + κ / 2) *
        ∑ z ∈ (sourceUpperSupportedWindowIndices t s).image
          (integerDeficitWindowIndex (sourceUpperTarget t s - t + 1)),
          sourceUpperIntegerWindowKernel t s (κ / 4) L z := by
  exact source_upper_integer_window_sum t s κ L _ ht hκ hd hL
    (fun i hi ↦ (Finset.mem_filter.mp hi).2.2)

end SRWTightness
