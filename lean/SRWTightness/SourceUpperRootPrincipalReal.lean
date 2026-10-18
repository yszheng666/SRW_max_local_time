import SRWTightness.SourceUpperSupportedPrincipalReal

open scoped ENNReal

namespace SRWTightness

/-- The real root/window contribution is nonnegative on the true supported index set. -/
theorem source_upper_root_terminal_contribution_nonneg (t s K κ B C : ℝ) (b : Site)
    (M : ℕ) (hK : 1 ≤ K) (hs : 0 ≤ s) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hd : 0 ≤ upperTerminalDepth (sourceUpperLogRadius t)) :
    0 ≤ sourceUpperRootTerminalContribution t s K κ B C b M
      (sourceUpperSupportedWindowIndices t s) := by
  have hden : 1 ≤ (sourceUpperBlockRoot t b : ℝ) + K := by
    linarith [Nat.cast_nonneg (α := ℝ) (sourceUpperBlockRoot t b)]
  have hρ : 0 ≤ 1 - 1 / ((sourceUpperBlockRoot t b : ℝ) + K) := by
    have hh := (div_le_one (by linarith : 0 < (sourceUpperBlockRoot t b : ℝ) + K)).mpr hden
    linarith
  unfold sourceUpperRootTerminalContribution
  apply Finset.sum_nonneg
  intro J hJ
  apply mul_nonneg (pow_nonneg hρ _)
  exact Finset.sum_nonneg (fun i hi ↦
    source_upper_supported_window_product_nonneg t s B C κ b J i hs hB hC hd hi)

/-- Finite geometrically weighted ENNReal principal sums equal the verified real root/window kernel. -/
theorem source_upper_root_principal_real (t s K κ B C : ℝ) (b : Site) (M : ℕ)
    (hK : 1 ≤ K) (hs : 0 ≤ s) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hd : 0 ≤ upperTerminalDepth (sourceUpperLogRadius t)) :
    (∑ J ∈ Finset.range M,
      ENNReal.ofReal ((1 - 1 / ((sourceUpperBlockRoot t b : ℝ) + K)) ^ (J - 1)) *
        sourceUpperSupportedPrincipalSum t s C κ B b J) =
      ENNReal.ofReal (sourceUpperRootTerminalContribution t s K κ B C b M
        (sourceUpperSupportedWindowIndices t s)) := by
  have hden : 1 ≤ (sourceUpperBlockRoot t b : ℝ) + K := by
    linarith [Nat.cast_nonneg (α := ℝ) (sourceUpperBlockRoot t b)]
  have hρ : 0 ≤ 1 - 1 / ((sourceUpperBlockRoot t b : ℝ) + K) := by
    have hh := (div_le_one (by linarith : 0 < (sourceUpperBlockRoot t b : ℝ) + K)).mpr hden
    linarith
  have hinner (J : ℕ) : 0 ≤ ∑ i ∈ sourceUpperSupportedWindowIndices t s,
      sourceUpperTerminalWindowWeight t s C κ (t - 1 + (i : ℝ)) *
        sourceUpperBranchingWindowFactor t s B (sourceUpperBlockRoot t b) J
          (t - 1 + (i : ℝ)) :=
    Finset.sum_nonneg (fun i hi ↦
      source_upper_supported_window_product_nonneg t s B C κ b J i hs hB hC hd hi)
  rw [sourceUpperRootTerminalContribution,
    ENNReal.ofReal_sum_of_nonneg (fun J _ ↦ mul_nonneg (pow_nonneg hρ _) (hinner J))]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [source_upper_supported_principal_real t s B C κ b J hs hB hC hd,
    ENNReal.ofReal_mul (pow_nonneg hρ _)]

end SRWTightness
