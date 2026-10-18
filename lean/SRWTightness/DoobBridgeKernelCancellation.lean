import SRWTightness.BesselThreeKernel

namespace SRWTightness

/-- The terminal Doob factor cancels the linear factors in the Bessel bridge ratio. -/
theorem doob_bridge_kernel_cancellation (T s x y z : ℝ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    (z / x) * (besselThreeDensity (T - s) z y / besselThreeDensity T x y) =
      killedBrownianDensity (T - s) z y / killedBrownianDensity T x y := by
  unfold besselThreeDensity
  by_cases h : killedBrownianDensity T x y = 0
  · simp [h]
  · field_simp
    <;> ring

end SRWTightness
