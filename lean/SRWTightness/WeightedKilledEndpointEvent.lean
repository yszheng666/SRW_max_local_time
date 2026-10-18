import SRWTightness.KilledBrownianFirstMoment

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- A linearly weighted killed endpoint event has the exact Bessel probability factor. -/
theorem weighted_killed_endpoint_event (s x z : ℝ) (hs : 0 < s) (hx : 0 < x) (hz : 0 < z)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫ y, B.indicator (fun y ↦ y / x) y ∂killedBrownianDensityLaw s z) =
      (z / x) * (besselDensityLaw s z).real B := by
  classical
  have he (y : ℝ) : B.indicator (fun y ↦ y / x) y =
      (z / x) * ((y / z) * B.indicator (fun _ ↦ (1 : ℝ)) y) := by
    by_cases hy : y ∈ B
    · simp only [Set.indicator_of_mem hy, mul_one]
      field_simp
    · simp only [Set.indicator_of_notMem hy, mul_zero]
  simp_rw [he]
  rw [integral_const_mul, killed_bessel_weighted_integral s z hs hz]
  congr 1
  exact integral_indicator_one hB

end SRWTightness
