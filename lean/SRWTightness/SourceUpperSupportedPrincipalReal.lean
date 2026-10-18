import SRWTightness.SourceUpperSupportedPrincipalSum
import SRWTightness.SourceUpperRootTerminalNormalized

open scoped ENNReal

namespace SRWTightness

/-- The actual finite terminal windows retain both the true deficit and branching cutoffs. -/
noncomputable def sourceUpperSupportedWindowIndices (t s : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (⌊2 * t + 1⌋₊ + 1)).filter (fun i : ℕ ↦
    -(7 + s + upperTerminalDepth (sourceUpperLogRadius t) ^ (1 / 4 : ℝ)) ≤
      sourceUpperTarget t s - (t - 1 + (i : ℝ)) ∧
      t - 1 + (i : ℝ) ≤ sourceUpperBranchingEnd t s)

/-- Each supported real window contribution is nonnegative. -/
theorem source_upper_supported_window_product_nonneg (t s B C κ : ℝ) (b : Site) (J i : ℕ)
    (hs : 0 ≤ s) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hd : 0 ≤ upperTerminalDepth (sourceUpperLogRadius t))
    (hi : i ∈ sourceUpperSupportedWindowIndices t s) :
    0 ≤ sourceUpperTerminalWindowWeight t s C κ (t - 1 + (i : ℝ)) *
      sourceUpperBranchingWindowFactor t s B (sourceUpperBlockRoot t b) J
        (t - 1 + (i : ℝ)) := by
  have hu := (Finset.mem_filter.mp hi).2.2
  have hslack : 0 ≤ sourceUpperBranchingSlack t s (t - 1 + (i : ℝ)) := by
    unfold sourceUpperBranchingSlack
    linarith
  have hW : 0 ≤ sourceUpperTerminalWindowWeight t s C κ (t - 1 + (i : ℝ)) := by
    unfold sourceUpperTerminalWindowWeight
    positivity
  have hF : 0 ≤ sourceUpperBranchingWindowFactor t s B (sourceUpperBlockRoot t b) J
      (t - 1 + (i : ℝ)) := by
    unfold sourceUpperBranchingWindowFactor
    positivity
  exact mul_nonneg hW hF

/-- The supported ENNReal principal sum is exactly the ofReal of its real window sum. -/
theorem source_upper_supported_principal_real (t s B C κ : ℝ) (b : Site) (J : ℕ)
    (hs : 0 ≤ s) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hd : 0 ≤ upperTerminalDepth (sourceUpperLogRadius t)) :
    sourceUpperSupportedPrincipalSum t s C κ B b J =
      ENNReal.ofReal (∑ i ∈ sourceUpperSupportedWindowIndices t s,
        sourceUpperTerminalWindowWeight t s C κ (t - 1 + (i : ℝ)) *
          sourceUpperBranchingWindowFactor t s B (sourceUpperBlockRoot t b) J
            (t - 1 + (i : ℝ))) := by
  classical
  rw [ENNReal.ofReal_sum_of_nonneg (fun i hi ↦
    source_upper_supported_window_product_nonneg t s B C κ b J i hs hB hC hd hi)]
  unfold sourceUpperSupportedPrincipalSum sourceUpperSupportedWindowIndices
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs with h
  · rw [ENNReal.ofReal_mul (show
      0 ≤ sourceUpperTerminalWindowWeight t s C κ (t - 1 + (i : ℝ)) by
      unfold sourceUpperTerminalWindowWeight
      positivity)]
  · simp

end SRWTightness
