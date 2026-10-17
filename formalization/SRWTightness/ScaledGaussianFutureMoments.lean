import SRWTightness.ScaledGaussianFutureIndependence

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Scaled Brownian increments have zero mean. -/
theorem scaled_gaussian_increment_mean (T r t : ℝ) (hT : 0 < T)
    (hr : 0 ≤ r) (hrt : r ≤ t) (ht : t ≤ T) :
    (∫ ω, Real.sqrt T * gaussianDyadicPath ω (t / T) -
      Real.sqrt T * gaussianDyadicPath ω (r / T) ∂gaussianCoefficientLaw) = 0 := by
  simp_rw [← mul_sub]
  rw [integral_const_mul,
    gaussian_path_increment_mean (r / T) (t / T) (div_nonneg hr hT.le)
      ((div_le_div_iff_of_pos_right hT).mpr hrt) ((div_le_one hT).mpr ht), mul_zero]

/-- Scaled Brownian future increments have Brownian covariance in elapsed time. -/
theorem scaled_gaussian_future_covariance (T r u v : ℝ) (hT : 0 < T) (hr : 0 ≤ r)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hru : r + u ≤ T) (hrv : r + v ≤ T) :
    cov[fun ω ↦ Real.sqrt T * gaussianDyadicPath ω ((r + u) / T) -
        Real.sqrt T * gaussianDyadicPath ω (r / T),
      fun ω ↦ Real.sqrt T * gaussianDyadicPath ω ((r + v) / T) -
        Real.sqrt T * gaussianDyadicPath ω (r / T); gaussianCoefficientLaw] = min u v := by
  have hrT : r ≤ T := by linarith
  have hru0 : 0 ≤ r + u := add_nonneg hr hu
  have hrv0 : 0 ≤ r + v := add_nonneg hr hv
  have hm (w : Set.Icc (0 : ℝ) T) :=
    ((scaled_gaussian_path_process T hT).hasGaussianLaw_eval w).memLp_two
  rw [covariance_fun_sub_fun_sub (hm ⟨r + u, hru0, hru⟩) (hm ⟨r, hr, hrT⟩)
    (hm ⟨r + v, hrv0, hrv⟩) (hm ⟨r, hr, hrT⟩),
    scaled_gaussian_path_covariance T (r + u) (r + v) hT hru0 hru hrv0 hrv,
    scaled_gaussian_path_covariance T (r + u) r hT hru0 hru hr hrT,
    scaled_gaussian_path_covariance T r (r + v) hT hr hrT hrv0 hrv,
    scaled_gaussian_path_covariance T r r hT hr hrT hr hrT,
    min_eq_right (by linarith : r ≤ r + u),
    min_eq_left (by linarith : r ≤ r + v), min_self]
  rcases le_total u v with h | h
  · rw [min_eq_left h, min_eq_left (by linarith : r + u ≤ r + v)]
    ring
  · rw [min_eq_right h, min_eq_right (by linarith : r + v ≤ r + u)]
    ring

end SRWTightness
