import SRWTightness.DiskExitPotentialBound

open MeasureTheory Filter

namespace SRWTightness

theorem normSq_sub_lower_of_inner (R : ℝ) (hR : 0 ≤ R) (w y : Site)
    (hw : R ^ 2 ≤ normSq w) (hy : normSq y ≤ (R / 2) ^ 2) :
    (R / 2) ^ 2 ≤ normSq (w - y) := by
  have hs := Real.sq_sqrt (normSq_nonneg (w - y))
  have hr := Real.sqrt_nonneg (normSq (w - y))
  have ht := normSq_add_bound (w - y) y hr (by positivity : 0 ≤ R / 2) hs.ge hy
  rw [sub_add_cancel] at ht
  by_contra h
  have hl : Real.sqrt (normSq (w - y)) < R / 2 := by nlinarith
  nlinarith

theorem exitPayoff_potential_disk_lower (R : ℝ) (hR : 0 < R) (y : Site)
    (hy : normSq y ≤ (R / 2) ^ 2) :
    (2 / Real.pi) * Real.log (R / 2) - potentialLowerConstant ≤
      exitPayoff (diskFinset R) (fun w ↦ potentialKernel (w - y)) 0 := by
  unfold exitPayoff
  calc
    _ = ∫ _ω : Sample, (2 / Real.pi) * Real.log (R / 2) - potentialLowerConstant ∂pathLaw := by simp
    _ ≤ _ := by
      apply integral_mono_ae (integrable_const _) (integrable_domainExit_payoff (diskFinset R) 0 (fun w ↦ potentialKernel (w - y)))
      filter_upwards [normSq_exitSteps_bounds hR.le] with ω hω
      have hb := normSq_sub_lower_of_inner R hR.le (position ω (exitSteps R ω)) y hω.1 hy
      have hr : R / 2 ≤ Real.sqrt (normSq (position ω (exitSteps R ω) - y)) :=
        (Real.le_sqrt (by positivity) (normSq_nonneg _)).mpr hb
      have hlog := Real.log_le_log (by positivity : 0 < R / 2) (hr.trans (le_max_left _ (1 : ℝ)))
      have hl := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 2 / Real.pi)
      have hp := potentialKernel_ge_log_radius (position ω (exitSteps R ω) - y)
      simp only [domainExitLocation, domainSteps_disk, zero_add]
      linarith

end SRWTightness
