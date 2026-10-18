import SRWTightness.HarmonicVarianceError

namespace SRWTightness

/-- Fixed proportions of the terminal depth control both harmonic variance scales. -/
theorem source_upper_variance_scales (d h v₀ K B : ℝ)
    (hd : 0 < d) (hhL : d / 8 ≤ h) (hhU : h ≤ d / 2)
    (hK : 0 ≤ K) (hB : 0 ≤ B) (hsmall : B + 3 * K ≤ d / 8)
    (herr : |v₀ - (d - h)| ≤ B) :
    0 < v₀ ∧ K ≤ v₀ ∧
      d / 8 ≤ (1 + K / v₀) ^ 2 * v₀ ∧
      (1 + K / v₀) ^ 2 * v₀ ≤ 2 * d ∧
      |(1 + K / v₀) ^ 2 * v₀ - (d - h)| ≤ B + 3 * K := by
  have he := abs_le.mp herr
  have hv₀ : 0 < v₀ := by linarith
  have hKv : K ≤ v₀ := by linarith
  have hv := gaussian_regression_enlarged_variance v₀ K hv₀ hK hKv
  refine ⟨hv₀, hKv, ?_, ?_, ?_⟩
  · linarith [hv.1]
  · linarith [hv.2]
  · exact harmonic_enlarged_variance_error v₀ K d h B hv₀ hK hKv herr

end SRWTightness
