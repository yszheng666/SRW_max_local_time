import SRWTightness.SourceUpperPrincipalErrorTotal
import SRWTightness.SourceUpperSpatialRemainderDecay

open Filter

namespace SRWTightness

/-- The positive-root spatial total has the desired height tail plus an explicit vanishing error. -/
theorem source_upper_principal_error_decay (hScale : ExponentialFloorScaleInput)
    (K κ C ρ : ℝ) (hK : 1 ≤ K) (hκ : 0 < κ) (hC : 0 ≤ C) (hρ : 0 < ρ) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ t : ℝ in atTop, ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t →
      ∀ B : ℝ, 0 ≤ B → ∀ N : ℕ,
      (∑ b ∈ sourceUpperBlockCenters t, ∑ J ∈ Finset.Icc 1 N,
        ENNReal.ofReal ((1 - 1 / ((sourceUpperBlockRoot t b : ℝ) + K)) ^ (J - 1)) *
          (sourceUpperSupportedPrincipalSum t s C κ B b J +
            ENNReal.ofReal (sourceUpperTerminalRemainder t C ρ))) ≤
        ENNReal.ofReal (D * B * C * (1 + s) * Real.exp (-(2 * Real.sqrt Real.pi * s))) +
          ENNReal.ofReal (50 * C * Real.exp (-2 * t)) := by
  obtain ⟨D, hD, hp⟩ := source_upper_principal_error_total hScale K κ hK hκ
  refine ⟨D, hD, ?_⟩
  filter_upwards [hp, source_upper_spatial_remainder_decay hScale K C ρ hK hC hρ]
    with t hp he
  intro s hs hslog B hB N
  have hK0 : 0 ≤ K := by linarith
  have hE : 0 ≤ sourceUpperTerminalRemainder t C ρ := by
    unfold sourceUpperTerminalRemainder
    positivity
  apply (hp s hs hslog B C _ hB hC hE N).trans
  apply add_le_add le_rfl
  rw [← ENNReal.ofReal_sum_of_nonneg (fun b _ ↦
    mul_nonneg (by positivity : 0 ≤ (sourceUpperBlockRoot t b : ℝ) + K) hE)]
  exact ENNReal.ofReal_le_ofReal he

end SRWTightness
