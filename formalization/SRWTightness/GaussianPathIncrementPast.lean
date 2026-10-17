import SRWTightness.ActualUnitBridge

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The actual unit Brownian past and a later increment form a joint Gaussian process. -/
theorem gaussian_path_past_increment_gaussian (s t : ℝ)
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    IsGaussianProcess
      (Sum.elim (fun u : Set.Icc (0 : ℝ) s ↦ fun ω ↦ gaussianDyadicPath ω u)
        (fun _ : Unit ↦ fun ω ↦ gaussianDyadicPath ω t - gaussianDyadicPath ω s))
      gaussianCoefficientLaw := by
  classical
  let a : Set.Icc (0 : ℝ) 1 := ⟨s, hs, hst.trans ht⟩
  let b : Set.Icc (0 : ℝ) 1 := ⟨t, hs.trans hst, ht⟩
  apply gaussianPath_unit_gaussianProcess.of_isGaussianProcess
  rintro (u | v)
  · let c : Set.Icc (0 : ℝ) 1 := ⟨u, u.property.1, u.property.2.trans (hst.trans ht)⟩
    exact ⟨{c}, ContinuousLinearMap.proj ⟨c, by simp⟩, by intro ω; rfl⟩
  · exact ⟨{a, b},
      { toFun z := z ⟨b, by simp⟩ - z ⟨a, by simp⟩
        map_add' z w := by simp; ring
        map_smul' c z := by simp; ring }, by intro ω; rfl⟩

/-- A later actual Brownian increment is independent of the whole earlier path. -/
theorem gaussian_path_increment_indep_past (s t : ℝ)
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    IndepFun (fun ω (u : Set.Icc (0 : ℝ) s) ↦ gaussianDyadicPath ω u)
      (fun ω ↦ gaussianDyadicPath ω t - gaussianDyadicPath ω s) gaussianCoefficientLaw := by
  have hg := gaussian_path_past_increment_gaussian s t hs hst ht
  have hc (u : Set.Icc (0 : ℝ) s) :
      cov[fun ω ↦ gaussianDyadicPath ω u,
        fun ω ↦ gaussianDyadicPath ω t - gaussianDyadicPath ω s;
        gaussianCoefficientLaw] = 0 := by
    have hm (v : Set.Icc (0 : ℝ) 1) :=
      (gaussianPath_unit_gaussianProcess.hasGaussianLaw_eval v).memLp_two
    rw [covariance_fun_sub_right
      (hm ⟨u, u.property.1, u.property.2.trans (hst.trans ht)⟩)
      (hm ⟨t, hs.trans hst, ht⟩) (hm ⟨s, hs, hst.trans ht⟩),
      gaussianPath_covariance u t u.property.1 (u.property.2.trans (hst.trans ht))
        (hs.trans hst) ht,
      gaussianPath_covariance u s u.property.1 (u.property.2.trans (hst.trans ht))
        hs (hst.trans ht),
      min_eq_left (u.property.2.trans hst), min_eq_left u.property.2, sub_self]
  have hh := IsGaussianProcess.indepFun_of_covariance_eq_zero hg
    (fun u ↦ (gaussianDyadicPath_measurable u).aemeasurable)
    (fun _ ↦ ((gaussianDyadicPath_measurable t).sub
      (gaussianDyadicPath_measurable s)).aemeasurable) (fun u _ ↦ hc u)
  exact hh.comp measurable_id (measurable_pi_apply ())

end SRWTightness
