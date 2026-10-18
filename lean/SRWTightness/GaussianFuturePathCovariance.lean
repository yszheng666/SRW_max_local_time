import SRWTightness.GaussianPathIncrementLaw

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Future Brownian increments have Brownian covariance in elapsed time. -/
theorem gaussian_future_path_covariance (s u v : ℝ) (hs : 0 ≤ s)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hsu : s + u ≤ 1) (hsv : s + v ≤ 1) :
    cov[fun ω ↦ gaussianDyadicPath ω (s + u) - gaussianDyadicPath ω s,
      fun ω ↦ gaussianDyadicPath ω (s + v) - gaussianDyadicPath ω s;
      gaussianCoefficientLaw] = min u v := by
  have hs1 : s ≤ 1 := by linarith
  have hsu0 : 0 ≤ s + u := add_nonneg hs hu
  have hsv0 : 0 ≤ s + v := add_nonneg hs hv
  have hm (w : Set.Icc (0 : ℝ) 1) :=
    (gaussianPath_unit_gaussianProcess.hasGaussianLaw_eval w).memLp_two
  rw [covariance_fun_sub_fun_sub (hm ⟨s + u, hsu0, hsu⟩) (hm ⟨s, hs, hs1⟩)
    (hm ⟨s + v, hsv0, hsv⟩) (hm ⟨s, hs, hs1⟩),
    gaussianPath_covariance (s + u) (s + v) hsu0 hsu hsv0 hsv,
    gaussianPath_covariance (s + u) s hsu0 hsu hs hs1,
    gaussianPath_covariance s (s + v) hs hs1 hsv0 hsv,
    gaussianPath_covariance s s hs hs1 hs hs1,
    min_eq_right (by linarith : s ≤ s + u),
    min_eq_left (by linarith : s ≤ s + v), min_self]
  rcases le_total u v with h | h
  · rw [min_eq_left h, min_eq_left (by linarith : s + u ≤ s + v)]
    ring
  · rw [min_eq_right h, min_eq_right (by linarith : s + v ≤ s + u)]
    ring

end SRWTightness
