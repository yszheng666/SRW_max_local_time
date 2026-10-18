import SRWTightness.SourceUpperGaussianPrefactor

namespace SRWTightness

/-- An explicit radius threshold makes the square-root height loss smaller than the variance. -/
theorem source_upper_gaussian_mills_large_scale (η B d : ℝ) (hη : 0 < η)
    (hd : 0 < d) (hscale : 4 / η ^ 2 ≤ d) (herror : 6 * B / η ≤ d) :
    Real.sqrt d + 3 * B ≤ η * d := by
  have hsq : 4 ≤ d * η ^ 2 := (div_le_iff₀ (by positivity)).mp hscale
  have hsqD := mul_le_mul_of_nonneg_left hsq hd.le
  have hs : Real.sqrt d ≤ η * d / 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith only [hsqD]
  have hb : 6 * B ≤ d * η := (div_le_iff₀ hη).mp herror
  linarith only [hs, hb]

/-- The manuscript range q>=-sqrt d satisfies the Mills threshold for all large scales. -/
theorem source_upper_gaussian_mills_source_threshold (a v d h q δ ε η B : ℝ)
    (hη : 0 < η) (hd : 0 < d) (hh : 1 ≤ h) (hvD : η * d ≤ v)
    (hscale : 4 / η ^ 2 ≤ d) (herror : 6 * B / η ≤ d)
    (hq : -Real.sqrt d ≤ q)
    (ha : a = 2 * (d - h) + q + (3 / 4 : ℝ) * Real.log h + δ)
    (hv : v = d - h + ε) (hδ : -B ≤ δ) (hε : ε ≤ B) : v ≤ a := by
  have hlarge := source_upper_gaussian_mills_large_scale η B d hη hd hscale herror
  have hres := source_upper_gaussian_residual_height a v d h q δ ε B ha hv hδ hε hh
  linarith only [hlarge, hres, hvD, hq]

end SRWTightness
