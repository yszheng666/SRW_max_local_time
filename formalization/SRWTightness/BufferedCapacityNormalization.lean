import SRWTightness.BufferedAnnulusCapacity
import SRWTightness.SourceEntranceRelative

namespace SRWTightness

/-- A positive denominator perturbed by at most half changes the normalized inverse
by at most two. -/
theorem inverse_perturbation_ratio (α δ : ℝ) (hα : 0 < α) (hδ : |δ| ≤ α / 2) :
    1 / 2 ≤ α * (α + δ)⁻¹ ∧ α * (α + δ)⁻¹ ≤ 2 := by
  have hd := abs_le.mp hδ
  have hp : 0 < α + δ := by linarith
  rw [← div_eq_mul_inv]
  constructor
  · apply (le_div_iff₀ hp).mpr
    linarith
  · apply (div_le_iff₀ hp).mpr
    linarith

/-- The actual enclosing-disk capacity is uniformly comparable to the reciprocal reference time. -/
theorem buffered_capacity_normalization (hinput : PotentialKernelAsymptoticInput) :
    ∃ T : ℝ, 128 ≤ T ∧ ∀ m H : ℝ, T ≤ m → 0 ≤ H → H ≤ m / 8 → ∀ b : Site,
      let α := (2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H))
      let cap := capacity (translateFinset b (diskFinset (Real.exp 1 * m + H)))
        (translateFinset b (diskFinset (m - H)))
      1 / 2 ≤ α * cap ∧ α * cap ≤ 2 := by
  obtain ⟨L, T, hL, hT, hh⟩ := buffered_annulus_capacity hinput
  let g : ℝ := 2 / Real.pi
  have hg : 0 < g := by dsimp [g]; positivity
  refine ⟨max 128 (max T (2 * L / g)), le_max_left _ _, ?_⟩
  intro m H hm hH hHm b
  have hm128 : 128 ≤ m := (le_max_left _ _).trans hm
  have hTm : T ≤ m := (le_max_left _ _).trans ((le_max_right _ _).trans hm)
  have hLm : 2 * L / g ≤ m := (le_max_right _ _).trans ((le_max_right _ _).trans hm)
  have hm0 : 0 < m := by linarith
  obtain ⟨δ, hδ, hcap⟩ := hh m H hTm hH (by linarith) b
  dsimp only
  rw [hcap]
  have hα := source_terminal_alpha_lower m H hm0 hH (by linarith)
  have hsmall : L / m ≤ g / 2 := by
    have hl := (div_le_iff₀ hg).mp hLm
    apply (div_le_iff₀ hm0).mpr
    nlinarith
  apply inverse_perturbation_ratio
  · exact hg.trans_le hα
  · exact hδ.trans (hsmall.trans (div_le_div_of_nonneg_right hα (by norm_num)))

end SRWTightness
