import SRWTightness.GaussianPathIncrementLaw

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The whole past and the whole future increment path are jointly Gaussian. -/
theorem gaussian_past_future_path_gaussian (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    IsGaussianProcess
      (Sum.elim (fun u : Set.Icc (0 : ℝ) s ↦ fun ω ↦ gaussianDyadicPath ω u)
        (fun t : Set.Icc s (1 : ℝ) ↦ fun ω ↦
          gaussianDyadicPath ω t - gaussianDyadicPath ω s)) gaussianCoefficientLaw := by
  classical
  let a : Set.Icc (0 : ℝ) 1 := ⟨s, hs, hs1⟩
  apply gaussianPath_unit_gaussianProcess.of_isGaussianProcess
  rintro (u | t)
  · let c : Set.Icc (0 : ℝ) 1 := ⟨u, u.property.1, u.property.2.trans hs1⟩
    exact ⟨{c}, ContinuousLinearMap.proj ⟨c, by simp⟩, by intro ω; rfl⟩
  · let b : Set.Icc (0 : ℝ) 1 := ⟨t, hs.trans t.property.1, t.property.2⟩
    exact ⟨{a, b},
      { toFun z := z ⟨b, by simp⟩ - z ⟨a, by simp⟩
        map_add' z w := by simp; ring
        map_smul' c z := by simp; ring }, by intro ω; rfl⟩

/-- The entire future Brownian increment path is independent of the entire past path. -/
theorem gaussian_future_path_indep_past (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    IndepFun (fun ω (u : Set.Icc (0 : ℝ) s) ↦ gaussianDyadicPath ω u)
      (fun ω (t : Set.Icc s (1 : ℝ)) ↦ gaussianDyadicPath ω t - gaussianDyadicPath ω s)
      gaussianCoefficientLaw := by
  apply IsGaussianProcess.indepFun_of_covariance_eq_zero
    (gaussian_past_future_path_gaussian s hs hs1)
    (fun u ↦ (gaussianDyadicPath_measurable u).aemeasurable)
    (fun t ↦ ((gaussianDyadicPath_measurable t).sub
      (gaussianDyadicPath_measurable s)).aemeasurable)
  intro u t
  have hm (v : Set.Icc (0 : ℝ) 1) :=
    (gaussianPath_unit_gaussianProcess.hasGaussianLaw_eval v).memLp_two
  rw [covariance_fun_sub_right
    (hm ⟨u, u.property.1, u.property.2.trans hs1⟩)
    (hm ⟨t, hs.trans t.property.1, t.property.2⟩) (hm ⟨s, hs, hs1⟩),
    gaussianPath_covariance u t u.property.1 (u.property.2.trans hs1)
      (hs.trans t.property.1) t.property.2,
    gaussianPath_covariance u s u.property.1 (u.property.2.trans hs1) hs hs1,
    min_eq_left (u.property.2.trans t.property.1), min_eq_left u.property.2, sub_self]

end SRWTightness
