import SRWTightness.UpperRootLayerSeries
import SRWTightness.SourceUpperSupportedPrincipalTotal
import SRWTightness.ExponentialFloorScaleProof

open Filter
open scoped ENNReal

namespace SRWTightness

/-- The literal root coefficient in the original principal series, with A=4+s. -/
theorem source_upper_original_root_series :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, 0 ≤ s →
      Summable (fun k : ℕ ↦ (1 + (4 + s) + (k : ℝ)) * ((k : ℝ) + 1) ^ 2 *
        Real.exp (-(9 * (k : ℝ) / 8))) ∧
      ∀ rate : ℝ, Real.exp (-rate * s) *
        (∑' k : ℕ, (1 + (4 + s) + (k : ℝ)) * ((k : ℝ) + 1) ^ 2 *
          Real.exp (-(9 * (k : ℝ) / 8))) ≤ C * (1 + s) * Real.exp (-rate * s) := by
  obtain ⟨C, hC, hh⟩ := upper_root_layer_series
  refine ⟨C, hC, ?_⟩
  intro s hs
  have hf : (fun k : ℕ ↦ (1 + (4 + s) + (k : ℝ)) * ((k : ℝ) + 1) ^ 2 *
      Real.exp (-(9 * (k : ℝ) / 8))) =
      (fun k : ℕ ↦ (5 + s + (k : ℝ)) * ((k : ℝ) + 1) ^ 2 *
        Real.exp (-(9 / 8 : ℝ) * k)) := by
    funext k
    congr 2 <;> ring
  rw [hf]
  obtain ⟨hSummable, hBound⟩ := hh s hs
  refine ⟨hSummable, ?_⟩
  intro rate
  exact (mul_le_mul_of_nonneg_left hBound (Real.exp_nonneg _)).trans_eq (by ring)

/-- The original principal rate supplied by the actual normalized kernel is positive. -/
theorem source_upper_original_principal_rate_pos : 0 < 2 * Real.sqrt Real.pi := by
  positivity

/-- The actual supported principal kernels obey the complete root-series bound internally. -/
theorem source_upper_original_supported_principal_bound (K κ : ℝ)
    (hK : 1 ≤ K) (hκ : 0 < κ) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ t : ℝ in atTop, ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t →
      ∀ B C : ℝ, 0 ≤ B → 0 ≤ C → ∀ M : ℕ,
      (∑ b ∈ sourceUpperBlockCenters t, ∑ J ∈ Finset.range M,
        ENNReal.ofReal ((1 - 1 / ((sourceUpperBlockRoot t b : ℝ) + K)) ^ (J - 1)) *
          sourceUpperSupportedPrincipalSum t s C κ B b J) ≤
        ENNReal.ofReal (D * B * C * (1 + s) * Real.exp (-(2 * Real.sqrt Real.pi * s))) := by
  exact source_upper_supported_principal_total exponential_floor_scale_input K κ hK hκ

end SRWTightness
