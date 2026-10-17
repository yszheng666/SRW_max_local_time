import SRWTightness.SourcePairShellSeries

namespace SRWTightness

/-- The standard quadratic exponential estimate absorbs the actual large-deficit shell sum. -/
theorem source_pair_shell_chernoff_uniform
    (hBound : QuadraticStretchedExponentialBoundInput) (γ : ℝ) (hγ : 0 < γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t A : ℝ),
      diskPointGaussianMinimumRadius ≤ A → sourceGaussianThreshold A ≤ t →
      sourceEquilibriumTimeError + sourceLowerTimeError + 1 ≤ Real.log A →
      ∀ (I : ℕ),
      (∀ j : ℕ, A * diskEnergyGapRatio ^ j ≤ sourceLowerRadius t / t ^ 6 ↔ j ≤ I) →
      let d := sourceLowerTime (sourceLowerRadius t)
      let h := fun i ↦ d - sourceObservationTime t A I (I - i + 1)
      (∑ i ∈ Finset.range (I + 1),
        if d / 2 < h i then d * Real.exp (-2 * (h i) ^ γ) else 0) ≤ C := by
  have hc : 0 < 2 * (1 / 2 : ℝ) ^ γ :=
    mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _)
  obtain ⟨C, hC, hb⟩ := hBound (2 * (1 / 2 : ℝ) ^ γ) γ hc hγ
  refine ⟨C, hC, ?_⟩
  intro t A hA ht hlog I hI
  dsimp only
  let d := sourceLowerTime (sourceLowerRadius t)
  have hd : 1 ≤ d := by
    have hh := (source_pair_shell_deficit_bounds t A hA ht hlog I hI).1 0 (Nat.zero_le I)
    exact hh.1.trans hh.2
  have he : (d / 2) ^ γ = (1 / 2 : ℝ) ^ γ * d ^ γ := by
    rw [show d / 2 = (1 / 2 : ℝ) * d by ring,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 2) (by linarith : 0 ≤ d)]
  have hs := source_pair_shell_chernoff_sum t A γ hγ.le hA ht hlog I hI
  dsimp only at hs
  change _ ≤ d ^ 2 * Real.exp (-2 * (d / 2) ^ γ) at hs
  rw [he] at hs
  have hp := hb d hd
  have heq : -2 * ((1 / 2 : ℝ) ^ γ * d ^ γ) =
      -(2 * (1 / 2 : ℝ) ^ γ) * d ^ γ := by ring
  rw [heq] at hs
  exact hs.trans hp

end SRWTightness
