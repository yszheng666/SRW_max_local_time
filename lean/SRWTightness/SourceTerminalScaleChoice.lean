import SRWTightness.SourceTerminalCutoffRange
import SRWTightness.SourceReferenceIntensityLimit

namespace SRWTightness

/-- A fixed sufficiently large inner radius admits a uniform terminal cutoff and variance range. -/
theorem source_terminal_scale_choice (H₀ A : ℝ)
    (hA : diskPointGaussianMinimumRadius ≤ A)
    (hlog : H₀ + sourceEquilibriumTimeError + sourceLowerTimeError ≤ Real.log A) :
    ∃ t₀ : ℝ, ∀ t : ℝ, t₀ ≤ t → ∀ (b : Site) (I : ℕ),
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) →
      sourceGaussianThreshold A ≤ t ∧
      let d := sourceLowerTime (sourceLowerRadius t)
      let H := d - sourceObservationTime t A I (I + 1)
      H ∈ Set.Icc H₀ (Real.log A + sourceEquilibriumTimeError + sourceLowerTimeError) ∧
      256 * H ≤ d ∧
      sourceObservationTime t A I (I + 2) - sourceObservationTime t A I (I + 1) ∈
        Set.Icc 1 (Real.log A + sourcePointEnergyTimeError + sourceEquilibriumTimeError) := by
  let Hmax := Real.log A + sourceEquilibriumTimeError + sourceLowerTimeError
  let t₀ := max (sourceGaussianThreshold A)
    (max (sourceScaleThreshold 4) (Real.exp (256 * Hmax + sourceLowerTimeError)))
  refine ⟨t₀, ?_⟩
  intro t ht b I hI
  have htG : sourceGaussianThreshold A ≤ t := (le_max_left _ _).trans ht
  have ht4 : sourceScaleThreshold 4 ≤ t :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ht)
  have htexp : Real.exp (256 * Hmax + sourceLowerTimeError) ≤ t :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ht)
  have hlogt := Real.log_le_log (Real.exp_pos _) htexp
  rw [Real.log_exp] at hlogt
  have htpos : 0 < t := (Real.exp_pos _).trans_le htexp
  have hlogm := Real.log_le_log htpos (sourceLowerRadius_ge_self t ht4)
  have hm70 := (sourceScaleThreshold_conditions t 4 (by norm_num) ht4).2.2.1
  have hd := (abs_le.mp (sourceLowerTime_log_bound (sourceLowerRadius t)
    (by linarith))).1
  have hcut := source_terminal_cutoff_range b t A hA htG I hI
  obtain ⟨hl, hu⟩ := abs_le.mp hcut.1
  refine ⟨htG, ?_⟩
  dsimp only
  refine ⟨⟨by linarith, by linarith⟩, ?_, hcut.2.1, hcut.2.2⟩
  dsimp [Hmax] at hlogt
  linarith

end SRWTightness
