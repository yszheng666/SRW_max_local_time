import SRWTightness.GaussianPathIncrementPast

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The actual unit Brownian increment has mean zero. -/
theorem gaussian_path_increment_mean (s t : ℝ)
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    (∫ ω, gaussianDyadicPath ω t - gaussianDyadicPath ω s ∂gaussianCoefficientLaw) = 0 := by
  have hm (u : Set.Icc (0 : ℝ) 1) :=
    (gaussianPath_unit_gaussianProcess.hasGaussianLaw_eval u).integrable
  rw [integral_sub (hm ⟨t, hs.trans hst, ht⟩) (hm ⟨s, hs, hst.trans ht⟩),
    (gaussianPath_eval_hasLaw t (hs.trans hst) ht).integral_eq,
    (gaussianPath_eval_hasLaw s hs (hst.trans ht)).integral_eq]
  simp [integral_id_gaussianReal]

/-- The actual unit Brownian increment has variance equal to its elapsed time. -/
theorem gaussian_path_increment_variance (s t : ℝ)
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    Var[fun ω ↦ gaussianDyadicPath ω t - gaussianDyadicPath ω s;
      gaussianCoefficientLaw] = t - s := by
  have hm (u : Set.Icc (0 : ℝ) 1) :=
    (gaussianPath_unit_gaussianProcess.hasGaussianLaw_eval u).memLp_two
  rw [variance_fun_sub (hm ⟨t, hs.trans hst, ht⟩) (hm ⟨s, hs, hst.trans ht⟩),
    gaussianPath_eval_variance t (hs.trans hst) ht,
    gaussianPath_eval_variance s hs (hst.trans ht),
    gaussianPath_covariance t s (hs.trans hst) ht hs (hst.trans ht), min_eq_right hst]
  ring

/-- The actual unit Brownian increment has the exact centered Gaussian law. -/
theorem gaussian_path_increment_law (s t : ℝ)
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    HasLaw (fun ω ↦ gaussianDyadicPath ω t - gaussianDyadicPath ω s)
      (gaussianReal 0 (t - s).toNNReal) gaussianCoefficientLaw := by
  have hG := gaussian_path_past_increment_gaussian s t hs hst ht
  have hh := (hG.hasGaussianLaw_eval (Sum.inr ())).map_eq_gaussianReal
  simp only [Sum.elim_inr] at hh
  rw [gaussian_path_increment_mean s t hs hst ht,
    gaussian_path_increment_variance s t hs hst ht] at hh
  exact ⟨((gaussianDyadicPath_measurable t).sub
    (gaussianDyadicPath_measurable s)).aemeasurable, hh⟩

end SRWTightness
