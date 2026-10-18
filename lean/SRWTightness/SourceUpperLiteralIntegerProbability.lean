import SRWTightness.SourceUpperLiteralIntegerPrincipal
import SRWTightness.SourceUpperRootPrincipalReal

open Filter
open scoped ENNReal

namespace SRWTightness

/-- The supported root-level probability kernels satisfy the literal original (4.29) formula. -/
theorem source_upper_literal_integer_probability (K κ : ℝ)
    (hK : 1 ≤ K) (hκ : 0 < κ) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ t : ℝ in atTop, ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t →
      ∀ B C : ℝ, 0 ≤ B → 0 ≤ C → ∀ M k : ℕ,
      let L : ℝ := (sourceUpperCoarseDepth t - k : ℕ)
      let d := upperTerminalDepth (sourceUpperLogRadius t)
      (∑ b ∈ sourceUpperBlockRootFamily t k, ∑ J ∈ Finset.range M,
        ENNReal.ofReal ((1 - 1 / ((sourceUpperBlockRoot t b : ℝ) + K)) ^ (J - 1)) *
          sourceUpperSupportedPrincipalSum t s C κ B b J) ≤
        ENNReal.ofReal (D * B * C * (1 + (4 + s) + (k : ℝ)) * ((k : ℝ) + 1) ^ 2 *
          Real.exp (2 * t - 2 * d) / L ^ 2 *
            sourceUpperLiteralIntegerSeries t s (κ / 4) L) := by
  obtain ⟨D, hD, hprincipal⟩ := source_upper_literal_integer_principal K κ hK hκ
  refine ⟨D, hD, ?_⟩
  filter_upwards [hprincipal, source_upper_terminal_sqrt_scale exponential_floor_scale_input]
    with t ht hd
  intro s hs hslog B C hB hC M k
  have hd0 : 0 ≤ upperTerminalDepth (sourceUpperLogRadius t) :=
    (Real.sqrt_pos.mp (by linarith [hd.1])).le
  have heq : (∑ b ∈ sourceUpperBlockRootFamily t k, ∑ J ∈ Finset.range M,
      ENNReal.ofReal ((1 - 1 / ((sourceUpperBlockRoot t b : ℝ) + K)) ^ (J - 1)) *
        sourceUpperSupportedPrincipalSum t s C κ B b J) =
      ENNReal.ofReal (∑ b ∈ sourceUpperBlockRootFamily t k,
        sourceUpperRootTerminalContribution t s K κ B C b M
          (sourceUpperSupportedWindowIndices t s)) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun b _ ↦
      source_upper_root_terminal_contribution_nonneg t s K κ B C b M hK hs hB hC hd0)]
    exact Finset.sum_congr rfl (fun b _ ↦
      source_upper_root_principal_real t s K κ B C b M hK hs hB hC hd0)
  rw [heq]
  exact ENNReal.ofReal_le_ofReal (ht s hs hslog B C hB hC M k)

end SRWTightness
