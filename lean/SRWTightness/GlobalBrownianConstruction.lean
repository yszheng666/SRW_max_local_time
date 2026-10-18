import SRWTightness.ActualIntervalBridge

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- A unit bridge time change gives an actual Brownian path on the entire nonnegative half-line. -/
noncomputable def globalBrownianPath (t : ℝ) (ω : GaussianCoefficientSpace) : ℝ :=
  (1 + max t 0) * actualUnitBridge (max t 0 / (1 + max t 0)) ω

/-- The time-changed unit-bridge clock always lies in its valid time interval. -/
theorem global_brownian_clock_mem (t : ℝ) :
    max t 0 / (1 + max t 0) ∈ Set.Icc (0 : ℝ) 1 := by
  have h : 0 < 1 + max t 0 := by positivity
  exact ⟨div_nonneg (le_max_right _ _) h.le, (div_le_one h).mpr (by linarith)⟩

/-- Each global Brownian evaluation is measurable. -/
theorem globalBrownianPath_measurable (t : ℝ) : Measurable (globalBrownianPath t) :=
  measurable_const.mul (actualUnitBridge_measurable _)

/-- The actual global construction starts at zero for every coefficient sample. -/
theorem globalBrownianPath_zero (ω : GaussianCoefficientSpace) : globalBrownianPath 0 ω = 0 := by
  simp [globalBrownianPath, actualUnitBridge_zero]

/-- The global construction has continuous paths,
including across its constant negative-time part. -/
theorem globalBrownianPath_continuous :
    ∀ᵐ ω ∂gaussianCoefficientLaw, Continuous (fun t ↦ globalBrownianPath t ω) := by
  filter_upwards [actualUnitBridge_continuous] with ω hω
  have hm : Continuous (fun t : ℝ ↦ max t 0) := continuous_id.max continuous_const
  have hd : Continuous (fun t : ℝ ↦ max t 0 / (1 + max t 0)) :=
    hm.div (continuous_const.add hm) (fun t ↦ ne_of_gt (by positivity))
  exact (continuous_const.add hm).mul (hω.comp hd)

/-- The global construction is a Gaussian process on all real times. -/
theorem globalBrownianPath_gaussian :
    IsGaussianProcess globalBrownianPath gaussianCoefficientLaw := by
  let f : ℝ → Set.Icc (0 : ℝ) 1 := fun t ↦ ⟨_, global_brownian_clock_mem t⟩
  exact (actualUnitBridge_gaussian.comp_right f).smul (fun t ↦ 1 + max t 0)

/-- The global Brownian construction is centered. -/
theorem globalBrownianPath_mean (t : ℝ) :
    (∫ ω, globalBrownianPath t ω ∂gaussianCoefficientLaw) = 0 := by
  unfold globalBrownianPath
  rw [integral_const_mul, actualUnitBridge_mean _ (global_brownian_clock_mem t).1
    (global_brownian_clock_mem t).2, mul_zero]

/-- The global construction has the exact Brownian covariance at every nonnegative pair of times. -/
theorem globalBrownianPath_covariance (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    cov[globalBrownianPath s, globalBrownianPath t; gaussianCoefficientLaw] = min s t := by
  have hs1 : 0 < 1 + s := by linarith
  have ht1 : 0 < 1 + t := by linarith
  have hsm : s / (1 + s) ∈ Set.Icc (0 : ℝ) 1 := by
    simpa only [max_eq_left hs] using global_brownian_clock_mem s
  have htm : t / (1 + t) ∈ Set.Icc (0 : ℝ) 1 := by
    simpa only [max_eq_left ht] using global_brownian_clock_mem t
  unfold globalBrownianPath
  rw [max_eq_left hs, max_eq_left ht, covariance_const_mul_left,
    covariance_const_mul_right, actualUnitBridge_covariance _ _ hsm.1 hsm.2 htm.1 htm.2]
  rcases le_total s t with h | h
  · have hc : s / (1 + s) ≤ t / (1 + t) := by
      apply (div_le_div_iff₀ hs1 ht1).mpr
      nlinarith
    rw [min_eq_left h, min_eq_left hc]
    field_simp
    <;> ring
  · have hc : t / (1 + t) ≤ s / (1 + s) := by
      apply (div_le_div_iff₀ ht1 hs1).mpr
      nlinarith
    rw [min_eq_right h, min_eq_right hc]
    field_simp
    <;> ring

end SRWTightness
