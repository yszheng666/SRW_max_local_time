import SRWTightness.HarmonicRegressionBounds

namespace SRWTightness

/-- Regression enlargement preserves a bounded reference variance error. -/
theorem harmonic_enlarged_variance_error (v K d h B : ℝ)
    (hv : 0 < v) (hK : 0 ≤ K) (hKv : K ≤ v)
    (herr : |v - (d - h)| ≤ B) :
    |(1 + K / v) ^ 2 * v - (d - h)| ≤ B + 3 * K := by
  have hb := abs_le.mp herr
  have he := gaussian_regression_enlarged_variance v K hv hK hKv
  rw [abs_le]
  constructor <;> linarith

end SRWTightness
