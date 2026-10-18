import SRWTightness.ActualIntervalBridge

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- The future bridge segment after subtracting the interpolation from its intermediate value. -/
noncomputable def intervalBridgeSuffixResidual (T r u : ℝ) (ω : GaussianCoefficientSpace) : ℝ :=
  actualIntervalBridge T (r + u) ω - ((T - r - u) / (T - r)) * actualIntervalBridge T r ω

/-- Each future bridge residual coordinate is measurable. -/
theorem intervalBridgeSuffixResidual_measurable (T r u : ℝ) :
    Measurable (intervalBridgeSuffixResidual T r u) :=
  (actualIntervalBridge_measurable T (r + u)).sub
    (measurable_const.mul (actualIntervalBridge_measurable T r))

/-- The whole bridge past and its future centered segment form a joint Gaussian process. -/
theorem interval_bridge_past_suffix_gaussian (T r : ℝ)
    (hT : 0 < T) (hr : 0 ≤ r) (hrT : r ≤ T) :
    IsGaussianProcess
      (Sum.elim (fun t : Set.Icc (0 : ℝ) r ↦ actualIntervalBridge T t)
        (fun u : Set.Icc (0 : ℝ) (T - r) ↦ intervalBridgeSuffixResidual T r u))
      gaussianCoefficientLaw := by
  classical
  let b : Set.Icc (0 : ℝ) T := ⟨r, hr, hrT⟩
  apply (actualIntervalBridge_gaussian T hT).of_isGaussianProcess
  rintro (t | u)
  · let a : Set.Icc (0 : ℝ) T := ⟨t, t.property.1, t.property.2.trans hrT⟩
    exact ⟨{a}, ContinuousLinearMap.proj ⟨a, by simp⟩, by intro ω; rfl⟩
  · let a : Set.Icc (0 : ℝ) T :=
      ⟨r + u, add_nonneg hr u.property.1, by linarith [u.property.2]⟩
    exact ⟨{a, b},
      { toFun z := z ⟨a, by simp⟩ - ((T - r - (u : ℝ)) / (T - r)) * z ⟨b, by simp⟩
        map_add' z w := by simp; ring
        map_smul' c z := by simp; ring }, by intro ω; rfl⟩

/-- Subtracting the interpolation leaves a zero-mean future bridge segment. -/
theorem interval_bridge_suffix_mean (T r u : ℝ)
    (hT : 0 < T) (hr : 0 ≤ r) (hrT : r ≤ T) (hu : 0 ≤ u) (huT : u ≤ T - r) :
    (∫ ω, intervalBridgeSuffixResidual T r u ω ∂gaussianCoefficientLaw) = 0 := by
  have hru : r + u ≤ T := by linarith
  have hi (t : Set.Icc (0 : ℝ) T) :=
    ((actualIntervalBridge_gaussian T hT).hasGaussianLaw_eval t).integrable
  unfold intervalBridgeSuffixResidual
  rw [integral_sub (hi ⟨r + u, add_nonneg hr hu, hru⟩)
      ((hi ⟨r, hr, hrT⟩).const_mul _), integral_const_mul,
    actualIntervalBridge_mean T (r + u) hT (add_nonneg hr hu) hru,
    actualIntervalBridge_mean T r hT hr hrT, mul_zero, sub_zero]

end SRWTightness
