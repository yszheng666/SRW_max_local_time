import SRWTightness.ScaledGaussianPathLaw
import SRWTightness.GaussianFuturePathIndependence

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- A scaled Brownian past and later increment segment are jointly Gaussian. -/
theorem scaled_gaussian_past_future_gaussian (T r t : ℝ) (hT : 0 < T)
    (hr : 0 ≤ r) (hrt : r ≤ t) (ht : t ≤ T) :
    IsGaussianProcess
      (Sum.elim (fun u : Set.Icc (0 : ℝ) r ↦ fun ω ↦
        Real.sqrt T * gaussianDyadicPath ω (u / T))
        (fun v : Set.Icc r t ↦ fun ω ↦
          Real.sqrt T * gaussianDyadicPath ω (v / T) -
            Real.sqrt T * gaussianDyadicPath ω (r / T))) gaussianCoefficientLaw := by
  classical
  let a : Set.Icc (0 : ℝ) T := ⟨r, hr, hrt.trans ht⟩
  apply (scaled_gaussian_path_process T hT).of_isGaussianProcess
  rintro (u | v)
  · let c : Set.Icc (0 : ℝ) T := ⟨u, u.property.1, u.property.2.trans (hrt.trans ht)⟩
    exact ⟨{c}, ContinuousLinearMap.proj ⟨c, by simp⟩, by intro ω; rfl⟩
  · let b : Set.Icc (0 : ℝ) T := ⟨v, hr.trans v.property.1, v.property.2.trans ht⟩
    exact ⟨{a, b},
      { toFun z := z ⟨b, by simp⟩ - z ⟨a, by simp⟩
        map_add' z w := by simp; ring
        map_smul' c z := by simp; ring }, by intro ω; rfl⟩

/-- The entire scaled Brownian increment segment is independent of the whole earlier path. -/
theorem scaled_gaussian_future_indep_past (T r t : ℝ) (hT : 0 < T)
    (hr : 0 ≤ r) (hrt : r ≤ t) (ht : t ≤ T) :
    IndepFun (fun ω (u : Set.Icc (0 : ℝ) r) ↦ Real.sqrt T * gaussianDyadicPath ω (u / T))
      (fun ω (v : Set.Icc r t) ↦ Real.sqrt T * gaussianDyadicPath ω (v / T) -
        Real.sqrt T * gaussianDyadicPath ω (r / T)) gaussianCoefficientLaw := by
  apply IsGaussianProcess.indepFun_of_covariance_eq_zero
    (scaled_gaussian_past_future_gaussian T r t hT hr hrt ht)
    (fun u ↦ (measurable_const.mul (gaussianDyadicPath_measurable _)).aemeasurable)
    (fun v ↦ ((measurable_const.mul (gaussianDyadicPath_measurable _)).sub
      (measurable_const.mul (gaussianDyadicPath_measurable _))).aemeasurable)
  intro u v
  have hm (w : Set.Icc (0 : ℝ) T) :=
    ((scaled_gaussian_path_process T hT).hasGaussianLaw_eval w).memLp_two
  have hrT := hrt.trans ht
  rw [covariance_fun_sub_right (hm ⟨u, u.property.1, u.property.2.trans hrT⟩)
    (hm ⟨v, hr.trans v.property.1, v.property.2.trans ht⟩) (hm ⟨r, hr, hrT⟩),
    scaled_gaussian_path_covariance T u v hT u.property.1 (u.property.2.trans hrT)
      (hr.trans v.property.1) (v.property.2.trans ht),
    scaled_gaussian_path_covariance T u r hT u.property.1 (u.property.2.trans hrT) hr hrT,
    min_eq_left (u.property.2.trans v.property.1), min_eq_left u.property.2, sub_self]

end SRWTightness
