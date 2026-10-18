import SRWTightness.SourceUpperRootPrincipalReal
import SRWTightness.SourceUpperRootTerminalTotal
import SRWTightness.SourceUpperTerminalSqrtScale

open Filter

namespace SRWTightness

/-- The supported principal probability kernels have the upper-tail scale after both finite sums. -/
theorem source_upper_supported_principal_total (hScale : ExponentialFloorScaleInput)
    (K κ : ℝ) (hK : 1 ≤ K) (hκ : 0 < κ) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ t : ℝ in atTop, ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t →
      ∀ B C : ℝ, 0 ≤ B → 0 ≤ C → ∀ M : ℕ,
      (∑ b ∈ sourceUpperBlockCenters t, ∑ J ∈ Finset.range M,
        ENNReal.ofReal ((1 - 1 / ((sourceUpperBlockRoot t b : ℝ) + K)) ^ (J - 1)) *
          sourceUpperSupportedPrincipalSum t s C κ B b J) ≤
        ENNReal.ofReal (D * B * C * (1 + s) * Real.exp (-(2 * Real.sqrt Real.pi * s))) := by
  classical
  obtain ⟨D, hD, ht⟩ := source_upper_root_terminal_total hScale K κ hK hκ
  refine ⟨D, hD, ?_⟩
  filter_upwards [ht, source_upper_terminal_sqrt_scale hScale] with t ht hd
  intro s hs hslog B C hB hC M
  have hd0 : 0 ≤ upperTerminalDepth (sourceUpperLogRadius t) :=
    (Real.sqrt_pos.mp (by linarith [hd.1])).le
  have heq : (∑ b ∈ sourceUpperBlockCenters t, ∑ J ∈ Finset.range M,
      ENNReal.ofReal ((1 - 1 / ((sourceUpperBlockRoot t b : ℝ) + K)) ^ (J - 1)) *
        sourceUpperSupportedPrincipalSum t s C κ B b J) =
      ENNReal.ofReal (∑ b ∈ sourceUpperBlockCenters t,
        sourceUpperRootTerminalContribution t s K κ B C b M
          (sourceUpperSupportedWindowIndices t s)) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun b _ ↦
      source_upper_root_terminal_contribution_nonneg t s K κ B C b M hK hs hB hC hd0)]
    exact Finset.sum_congr rfl (fun b _ ↦
      source_upper_root_principal_real t s K κ B C b M hK hs hB hC hd0)
  rw [heq]
  apply ENNReal.ofReal_le_ofReal
  exact ht s hs hslog B C hB hC M (sourceUpperSupportedWindowIndices t s)
    (fun i hi ↦ (Finset.mem_filter.mp hi).2)

end SRWTightness
