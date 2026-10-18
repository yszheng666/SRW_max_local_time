import SRWTightness.GaussianUnitProcess

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The actual unit Brownian path has the exact increment second moment. -/
theorem gaussian_unit_increment_second_moment (r s : ℝ)
    (hr : 0 ≤ r) (hrs : r ≤ s) (hs1 : s ≤ 1) :
    Integrable (fun ω ↦ (gaussianDyadicPath ω s - gaussianDyadicPath ω r) ^ 2)
      gaussianCoefficientLaw ∧
    (∫ ω, (gaussianDyadicPath ω s - gaussianDyadicPath ω r) ^ 2
      ∂gaussianCoefficientLaw) = s - r := by
  have hs := hr.trans hrs
  have hr1 := hrs.trans hs1
  have hm (v : Set.Icc (0 : ℝ) 1) :=
    (gaussianPath_unit_gaussianProcess.hasGaussianLaw_eval v).memLp_two
  have hms : MemLp (fun ω ↦ gaussianDyadicPath ω s) 2 gaussianCoefficientLaw := hm ⟨s, hs, hs1⟩
  have hmr : MemLp (fun ω ↦ gaussianDyadicPath ω r) 2 gaussianCoefficientLaw := hm ⟨r, hr, hr1⟩
  have hi : MemLp (fun ω ↦ gaussianDyadicPath ω s - gaussianDyadicPath ω r)
      2 gaussianCoefficientLaw := hms.sub hmr
  have hmean : (∫ ω, gaussianDyadicPath ω s - gaussianDyadicPath ω r
      ∂gaussianCoefficientLaw) = 0 := by
    rw [integral_sub (hms.integrable (by norm_num)) (hmr.integrable (by norm_num)),
      (gaussianPath_eval_hasLaw s hs hs1).integral_eq,
      (gaussianPath_eval_hasLaw r hr hr1).integral_eq]
    simp [integral_id_gaussianReal]
  refine ⟨hi.integrable_sq, ?_⟩
  have hv := variance_fun_sub hms hmr
  rw [gaussianPath_eval_variance s hs hs1, gaussianPath_eval_variance r hr hr1,
    gaussianPath_covariance s r hs hs1 hr hr1, min_eq_right hrs,
    variance_eq_integral hi.aemeasurable, hmean] at hv
  simpa only [sub_zero] using hv.trans (by ring)

end SRWTightness
