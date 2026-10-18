import SRWTightness.SourceUpperSupportedPrincipalTotal
import SRWTightness.UpperPositiveRootGeometricSum

open Filter

namespace SRWTightness

/-- Finite positive-root totals retain the terminal error multiplied by the spatial return scales. -/
theorem source_upper_principal_error_total (hScale : ExponentialFloorScaleInput)
    (K κ : ℝ) (hK : 1 ≤ K) (hκ : 0 < κ) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ t : ℝ in atTop, ∀ s : ℝ, 0 ≤ s → s ≤ Real.log t →
      ∀ B C E : ℝ, 0 ≤ B → 0 ≤ C → 0 ≤ E → ∀ N : ℕ,
      (∑ b ∈ sourceUpperBlockCenters t, ∑ J ∈ Finset.Icc 1 N,
        ENNReal.ofReal ((1 - 1 / ((sourceUpperBlockRoot t b : ℝ) + K)) ^ (J - 1)) *
          (sourceUpperSupportedPrincipalSum t s C κ B b J + ENNReal.ofReal E)) ≤
        ENNReal.ofReal (D * B * C * (1 + s) * Real.exp (-(2 * Real.sqrt Real.pi * s))) +
          ∑ b ∈ sourceUpperBlockCenters t,
            ENNReal.ofReal (((sourceUpperBlockRoot t b : ℝ) + K) * E) := by
  obtain ⟨D, hD, ht⟩ := source_upper_supported_principal_total hScale K κ hK hκ
  refine ⟨D, hD, ?_⟩
  filter_upwards [ht] with t ht
  intro s hs hslog B C E hB hC hE N
  conv_lhs => simp only [mul_add, Finset.sum_add_distrib]
  apply add_le_add
  · apply le_trans _ (ht s hs hslog B C hB hC (N + 1))
    apply Finset.sum_le_sum
    intro b hb
    apply Finset.sum_le_sum_of_subset
    intro J hJ
    have := (Finset.mem_Icc.mp hJ).2
    exact Finset.mem_range.mpr (by omega)
  · apply Finset.sum_le_sum
    intro b hb
    apply upper_positive_root_geometric_error _ E _ hE _
      (fun J hJ ↦ (Finset.mem_Icc.mp hJ).1)
    linarith [Nat.cast_nonneg (α := ℝ) (sourceUpperBlockRoot t b)]

end SRWTightness
