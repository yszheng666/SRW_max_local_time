import SRWTightness.SourceTerminalScaleChoice
import SRWTightness.SourceTerminalWindowConditions

namespace SRWTightness

/-- A single radius supplies terminal conditions and the logarithmic margin needed by pair estimates. -/
theorem source_terminal_application_conditions_with_log (H₀ ε : ℝ) (hε : 0 < ε) :
    ∃ A Hmax D t₀ : ℝ, diskPointGaussianMinimumRadius ≤ A ∧
      H₀ + sourceEquilibriumTimeError + sourceLowerTimeError ≤ Real.log A ∧ H₀ ≤ Hmax ∧ 1 ≤ D ∧
      ∀ t : ℝ, t₀ ≤ t → ∀ (b : Site) (I : ℕ),
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) →
      ∀ q : ℝ,
      let d := sourceLowerTime (sourceLowerRadius t)
      let T := sourceObservationTime t A I
      let H := d - T (I + 1)
      q ∈ Set.Icc (Real.sqrt d) (2 * Real.sqrt d) →
      sourceGaussianThreshold A ≤ t ∧ H ∈ Set.Icc H₀ Hmax ∧ 256 * H ≤ d ∧
      T (I + 2) - T (I + 1) ∈ Set.Icc 1 D ∧
      |sourceTerminalThreshold t (sourceTerminalRoot t q) - (2 * d + q)| ≤ ε ∧
      |sourcePointEnergyTime b (sourceLowerRadius t) 14 - d| ≤
        sourcePointEnergyTimeError + sourceLowerTimeError := by
  let A := max diskPointGaussianMinimumRadius
    (Real.exp (H₀ + sourceEquilibriumTimeError + sourceLowerTimeError))
  have hA : diskPointGaussianMinimumRadius ≤ A := le_max_left _ _
  have hlog : H₀ + sourceEquilibriumTimeError + sourceLowerTimeError ≤ Real.log A := by
    have hh := Real.log_le_log
      (Real.exp_pos (H₀ + sourceEquilibriumTimeError + sourceLowerTimeError))
      (show Real.exp (H₀ + sourceEquilibriumTimeError + sourceLowerTimeError) ≤ A from
        le_max_right _ _)
    simpa only [Real.log_exp] using hh
  obtain ⟨ts, hs⟩ := source_terminal_scale_choice H₀ A hA hlog
  obtain ⟨tw, hw⟩ := source_terminal_window_conditions ε hε
  let Hmax := max H₀ (Real.log A + sourceEquilibriumTimeError + sourceLowerTimeError)
  let D := max 1 (Real.log A + sourcePointEnergyTimeError + sourceEquilibriumTimeError)
  refine ⟨A, Hmax, D, max ts tw, hA, hlog, le_max_left _ _, le_max_left _ _, ?_⟩
  intro t ht b I hI q
  dsimp only
  intro hq
  have hc := hs t ((le_max_left _ _).trans ht) b I hI
  have he := hw t ((le_max_right _ _).trans ht) b q hq
  exact ⟨hc.1, ⟨hc.2.1.1, hc.2.1.2.trans (le_max_right _ _)⟩,
    hc.2.2.1, ⟨hc.2.2.2.1, hc.2.2.2.2.trans (le_max_right _ _)⟩, he⟩


/-- A single radius and time threshold supply the terminal Gaussian application conditions. -/
theorem source_terminal_application_conditions (H₀ ε : ℝ) (hε : 0 < ε) :
    ∃ A Hmax D t₀ : ℝ, diskPointGaussianMinimumRadius ≤ A ∧ H₀ ≤ Hmax ∧ 1 ≤ D ∧
      ∀ t : ℝ, t₀ ≤ t → ∀ (b : Site) (I : ℕ),
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) →
      ∀ q : ℝ,
      let d := sourceLowerTime (sourceLowerRadius t)
      let T := sourceObservationTime t A I
      let H := d - T (I + 1)
      q ∈ Set.Icc (Real.sqrt d) (2 * Real.sqrt d) →
      sourceGaussianThreshold A ≤ t ∧ H ∈ Set.Icc H₀ Hmax ∧ 256 * H ≤ d ∧
      T (I + 2) - T (I + 1) ∈ Set.Icc 1 D ∧
      |sourceTerminalThreshold t (sourceTerminalRoot t q) - (2 * d + q)| ≤ ε ∧
      |sourcePointEnergyTime b (sourceLowerRadius t) 14 - d| ≤
        sourcePointEnergyTimeError + sourceLowerTimeError := by
  obtain ⟨A, Hmax, D, t₀, hA, hlog, hH, hD, hconditions⟩ :=
    source_terminal_application_conditions_with_log H₀ ε hε
  exact ⟨A, Hmax, D, t₀, hA, hH, hD, hconditions⟩

end SRWTightness
