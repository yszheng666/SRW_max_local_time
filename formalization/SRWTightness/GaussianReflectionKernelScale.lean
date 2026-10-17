import SRWTightness.GaussianReflectionKernelBound

namespace SRWTightness

/-- In the late-time regime the reflection bound has inverse-time scale. -/
theorem gaussian_reflection_kernel_scale (d v q f e : ℝ) (l : ℕ)
    (hd : 0 < d) (hv : d / 2 ≤ v) (hq : 0 ≤ q)
    (hqu : q ≤ 2 * Real.sqrt d) (hf : 0 ≤ f)
    (he : 0 ≤ e) (heu : e ≤ 1 / 2) :
    (Real.sqrt (2 * Real.pi * v))⁻¹ * (2 * q * (f + l + 1 + 2 * e) / v) ≤
      16 * (f + l + 1) / d := by
  have hv0 : 0 < v := by linarith
  have hpi : 1 ≤ Real.pi := by linarith [Real.two_le_pi]
  have hvs : d ≤ 2 * Real.pi * v := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hpi) hv0.le]
  have hs := Real.sqrt_le_sqrt hvs
  have hs0 : 0 < Real.sqrt (2 * Real.pi * v) := by positivity
  have hq' : q ≤ 2 * Real.sqrt (2 * Real.pi * v) := by linarith
  have hl : 0 ≤ (l : ℝ) := Nat.cast_nonneg l
  have hF : 0 ≤ f + l + 1 := by linarith
  have hG : 0 ≤ f + l + 1 + 2 * e := by linarith
  have hGu : f + l + 1 + 2 * e ≤ 2 * (f + l + 1) := by linarith
  have hprod := mul_le_mul hq' hGu hG (by positivity :
    0 ≤ 2 * Real.sqrt (2 * Real.pi * v))
  calc
    _ = (2 * q * (f + l + 1 + 2 * e)) /
        (Real.sqrt (2 * Real.pi * v) * v) := by ring
    _ ≤ (8 * Real.sqrt (2 * Real.pi * v) * (f + l + 1)) /
        (Real.sqrt (2 * Real.pi * v) * v) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith
    _ = 8 * (f + l + 1) / v := by field_simp
    _ ≤ 16 * (f + l + 1) / d := by
      apply (div_le_div_iff₀ hv0 hd).mpr
      nlinarith [mul_nonneg hF (sub_nonneg.mpr hv)]

end SRWTightness
