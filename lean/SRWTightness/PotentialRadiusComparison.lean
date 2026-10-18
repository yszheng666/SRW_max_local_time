import SRWTightness.PotentialKernelRadialBounds

namespace SRWTightness

theorem potentialKernel_radius_lower (z : Site) (r : ℝ) (hr : 1 ≤ r)
    (hz : r ^ 2 ≤ normSq z) :
    (2 / Real.pi) * Real.log r - potentialLowerConstant ≤ potentialKernel z := by
  have hs : r ≤ Real.sqrt (normSq z) :=
    (Real.le_sqrt (by linarith : 0 ≤ r) (normSq_nonneg z)).mpr hz
  have hm : r ≤ max (Real.sqrt (normSq z)) 1 := hs.trans (le_max_left _ _)
  have hl := mul_le_mul_of_nonneg_left (Real.log_le_log (by linarith : 0 < r) hm)
    (by positivity : 0 ≤ 2 / Real.pi)
  exact (sub_le_sub_right hl _).trans (potentialKernel_ge_log_radius z)

theorem potentialKernel_radius_upper (z : Site) (r : ℝ) (hr : 1 ≤ r)
    (hz : normSq z ≤ r ^ 2) :
    potentialKernel z ≤ (2 / Real.pi) * Real.log r + potentialUpperConstant := by
  have hh := potentialKernel_le_log_normBound z (r ^ 2) (by nlinarith) hz
  rw [Real.log_pow] at hh
  convert hh using 1 <;> ring

end SRWTightness
