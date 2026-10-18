import SRWTightness.ActualIntervalBridge

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The centered prefix residual after removing the bridge's value at an intermediate time. -/
noncomputable def intervalBridgePrefixResidual (T r t : ℝ) (ω : GaussianCoefficientSpace) : ℝ :=
  actualIntervalBridge T t ω - (t / r) * actualIntervalBridge T r ω

/-- The prefix residual is measurable at every time. -/
theorem intervalBridgePrefixResidual_measurable (T r t : ℝ) :
    Measurable (intervalBridgePrefixResidual T r t) :=
  (actualIntervalBridge_measurable T t).sub
    (measurable_const.mul (actualIntervalBridge_measurable T r))

/-- The centered prefix and its intermediate endpoint form a joint Gaussian process. -/
theorem interval_bridge_prefix_joint_gaussian (T r : ℝ)
    (hT : 0 < T) (hr : 0 ≤ r) (hrT : r ≤ T) :
    IsGaussianProcess
      (Sum.elim (fun t : Set.Icc (0 : ℝ) r ↦ intervalBridgePrefixResidual T r t)
        (fun _ : Unit ↦ actualIntervalBridge T r)) gaussianCoefficientLaw := by
  classical
  let b : Set.Icc (0 : ℝ) T := ⟨r, hr, hrT⟩
  apply (actualIntervalBridge_gaussian T hT).of_isGaussianProcess
  rintro (t | u)
  · let a : Set.Icc (0 : ℝ) T := ⟨t, t.property.1, t.property.2.trans hrT⟩
    exact ⟨{a, b},
      { toFun z := z ⟨a, by simp⟩ - ((t : ℝ) / r) * z ⟨b, by simp⟩
        map_add' z w := by simp; ring
        map_smul' c z := by simp; ring }, by intro ω; rfl⟩
  · exact ⟨{b}, ContinuousLinearMap.proj ⟨b, by simp⟩, by intro ω; rfl⟩

/-- The centered prefix residual has zero mean. -/
theorem interval_bridge_prefix_mean (T r t : ℝ)
    (hT : 0 < T) (hr : 0 ≤ r) (hrT : r ≤ T) (ht : 0 ≤ t) (htr : t ≤ r) :
    (∫ ω, intervalBridgePrefixResidual T r t ω ∂gaussianCoefficientLaw) = 0 := by
  have hi (u : Set.Icc (0 : ℝ) T) :=
    ((actualIntervalBridge_gaussian T hT).hasGaussianLaw_eval u).integrable
  unfold intervalBridgePrefixResidual
  rw [integral_sub (hi ⟨t, ht, htr.trans hrT⟩) ((hi ⟨r, hr, hrT⟩).const_mul _),
    integral_const_mul, actualIntervalBridge_mean T t hT ht (htr.trans hrT),
    actualIntervalBridge_mean T r hT hr hrT, mul_zero, sub_zero]

/-- Conditioning at the intermediate time leaves exactly the shorter bridge covariance. -/
theorem interval_bridge_prefix_covariance (T r s t : ℝ)
    (hT : 0 < T) (hr : 0 < r) (hrT : r ≤ T)
    (hs : 0 ≤ s) (hsr : s ≤ r) (ht : 0 ≤ t) (htr : t ≤ r) :
    cov[intervalBridgePrefixResidual T r s, intervalBridgePrefixResidual T r t;
      gaussianCoefficientLaw] = min s t - s * t / r := by
  have hm (u : Set.Icc (0 : ℝ) T) :=
    ((actualIntervalBridge_gaussian T hT).hasGaussianLaw_eval u).memLp_two
  unfold intervalBridgePrefixResidual
  rw [covariance_fun_sub_fun_sub (hm ⟨s, hs, hsr.trans hrT⟩)
    ((hm ⟨r, hr.le, hrT⟩).const_mul _) (hm ⟨t, ht, htr.trans hrT⟩)
    ((hm ⟨r, hr.le, hrT⟩).const_mul _)]
  simp only [covariance_const_mul_left, covariance_const_mul_right]
  rw [actualIntervalBridge_covariance T s t hT hs (hsr.trans hrT) ht (htr.trans hrT),
    actualIntervalBridge_covariance T s r hT hs (hsr.trans hrT) hr.le hrT,
    actualIntervalBridge_covariance T r t hT hr.le hrT ht (htr.trans hrT),
    actualIntervalBridge_covariance T r r hT hr.le hrT hr.le hrT,
    min_eq_left hsr, min_eq_right htr, min_self]
  field_simp
  <;> ring

end SRWTightness
