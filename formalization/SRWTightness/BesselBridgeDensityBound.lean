import SRWTightness.BesselThreeKernelBounds

namespace SRWTightness

/-- Comparing the kernel time denominators on a half interval, with an explicit constant. -/
theorem bessel_kernel_time_comparison (T s : ℝ) (hT : 0 < T) (hs : 0 < s)
    (hTs : T ≤ 2 * s) :
    T * Real.sqrt (2 * Real.pi * T) ≤ 4 * (s * Real.sqrt (2 * Real.pi * s)) := by
  have hroot : Real.sqrt (2 * Real.pi * T) ≤ 2 * Real.sqrt (2 * Real.pi * s) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    have hsq := Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi * s)
    have hscale := mul_le_mul_of_nonneg_left hTs (by positivity : 0 ≤ 2 * Real.pi)
    nlinarith [Real.pi_pos]
  have h := mul_le_mul hTs hroot (Real.sqrt_nonneg _) (by positivity : 0 ≤ 2 * s)
  nlinarith

/-- The bridge restriction density is uniformly bounded before the midpoint.
The hypotheses only constrain the two bridge endpoints, not the intermediate position z. -/
theorem besselThree_bridge_density_bound (T s x y z M : ℝ)
    (hT : 0 < T) (hs : 0 < s) (hTs : T ≤ 2 * s)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : 2 * x * y / T ≤ 1) (hM : (x - y) ^ 2 / (2 * T) ≤ M) :
    besselThreeDensity s z y / besselThreeDensity T x y ≤ 8 * Real.exp M := by
  have hDT : 0 < T * Real.sqrt (2 * Real.pi * T) := by positivity
  have hDs : 0 < s * Real.sqrt (2 * Real.pi * s) := by positivity
  have htime := bessel_kernel_time_comparison T s hT hs hTs
  have hnum : besselThreeDensity s z y ≤ 8 * y ^ 2 /
      (T * Real.sqrt (2 * Real.pi * T)) := by
    apply (besselThreeDensity_upper s z y hs hz hy).trans
    apply (div_le_div_iff₀ hDs hDT).mpr
    nlinarith [mul_le_mul_of_nonneg_left htime (sq_nonneg y)]
  have he : Real.exp M * Real.exp (-M) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hlo := mul_le_mul_of_nonneg_left
    (besselThreeDensity_lower T x y M hT hx hy hxy hM)
    (by positivity : 0 ≤ 8 * Real.exp M)
  have hrewrite : 8 * Real.exp M *
      (Real.exp (-M) * y ^ 2 / (T * Real.sqrt (2 * Real.pi * T))) =
      8 * y ^ 2 / (T * Real.sqrt (2 * Real.pi * T)) := by
    calc
      _ = 8 * (Real.exp M * Real.exp (-M)) * y ^ 2 /
          (T * Real.sqrt (2 * Real.pi * T)) := by ring
      _ = _ := by rw [he]; ring
  rw [hrewrite] at hlo
  exact (div_le_iff₀ (besselThreeDensity_pos T x y hT hx hy)).mpr (hnum.trans hlo)

end SRWTightness
