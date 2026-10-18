import SRWTightness.SourceTerminalKProbabilityComplete
import SRWTightness.SourceGaussianTerminalSigma

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- A common source radius gives a positive c/d lower bound under the actual covariance. -/
theorem source_terminal_sigma_probability_lower_large (hReconstruct : BrownianBridgeReconstructionInput)
    (hGaussian : GaussianIntervalInput)
    (hReflection : BridgeReflectionInput) (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (Cm γ : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hIncrement : BesselThreeIncrementInput) (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2) :
    ∃ A c t₀ : ℝ, diskPointGaussianMinimumRadius ≤ A ∧ 0 < c ∧
      ∀ t : ℝ, t₀ ≤ t → ∀ (b : Site) (I : ℕ),
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) →
      ∀ q : ℝ,
      let d := sourceLowerTime (sourceLowerRadius t)
      let T := sourceObservationTime t A I
      let H := d - T (I + 1)
      let At := sourceTerminalThreshold t (sourceTerminalRoot t q)
      let V := sourcePointEnergyTime b (sourceLowerRadius t) 14
      q ∈ Set.Icc (Real.sqrt d) (2 * Real.sqrt d) →
      let e := geometricDiskPointError b A (Real.exp 1 * sourceLowerRadius t + 14)
        diskEnergyGapRatio (2 / Real.pi) (I + 1)
      let μ := (gaussianCoordinateLaw
        (brownianTimeMatrix T ((I + 1) + 1) - Matrix.diagonal e)).prod
        (independentBridgeLaw ℕ)
      let E := gaussianGridTerminalEvent T (I + 1) (q - Real.sqrt H - 1)
        (q - Real.sqrt H) At V q d γ
      c / d ≤ μ.real E := by
  obtain ⟨Hp, hHp, hp⟩ := gaussianGrid_terminal_probability_uniform hReconstruct hGaussian
    hReflection hBridge hReverse hPositive hInitial hHit Cm γ hMoment hγ hγhalf
  obtain ⟨Hs, hHs, hs⟩ := sourceGaussian_terminal_sigma_lower hReconstruct hGaussian
    hReflection hBridge hReverse hPositive hInitial hHit Cm γ hMoment hIncrement hγ hγhalf
  obtain ⟨A, Hmax, D, t₀, hA, hmax, hD, ha⟩ :=
    source_terminal_application_conditions (max Hp Hs) 1 (by norm_num)
  let K := max 0 (sourcePointEnergyTimeError + sourceLowerTimeError)
  obtain ⟨cp, Cp, hcp, hCp, hb⟩ := hp Hmax 1 K D
    ((le_max_left _ _).trans hmax) (by norm_num) (le_max_left _ _) hD
  obtain ⟨Cs, hCs, hc⟩ := hs Hmax 1 K D
    ((le_max_right _ _).trans hmax) (by norm_num) (le_max_left _ _) hD
  let w := Real.exp (-(Cs * ((diskEquilibriumWeightConstant / A) / (2 / Real.pi))) / 2)
  refine ⟨A, w * cp, t₀, hA, mul_pos (Real.exp_pos _) hcp, ?_⟩
  intro t ht b I hI q
  dsimp only
  intro hq
  have hh := ha t ht b I hI q hq
  have hgap := sourceObservationTime_gaps t A hA hh.1 I hI
  have hprob := hb (sourceObservationTime t A I) (I + 1) (by omega)
    (sourceObservationTime_zero t A I) hgap
    (sourceLowerTime (sourceLowerRadius t)) q
    (sourceTerminalThreshold t (sourceTerminalRoot t q))
    (sourcePointEnergyTime b (sourceLowerRadius t) 14)
    ⟨(le_max_left _ _).trans hh.2.1.1, hh.2.1.2⟩ hh.2.2.1 hq hh.2.2.2.2.1
    (hh.2.2.2.2.2.trans (le_max_right _ _))
    (by simpa only [Nat.add_assoc] using hh.2.2.2.1)
  have hsig := hc b t A hA hh.1 I hI
    (sourceLowerTime (sourceLowerRadius t)) q
    (sourceTerminalThreshold t (sourceTerminalRoot t q))
    (sourcePointEnergyTime b (sourceLowerRadius t) 14)
    ⟨(le_max_right _ _).trans hh.2.1.1, hh.2.1.2⟩ hh.2.2.1 hq hh.2.2.2.2.1
    (hh.2.2.2.2.2.trans (le_max_right _ _))
    (by simpa only [Nat.add_assoc] using hh.2.2.2.1)
  have hlo := mul_le_mul_of_nonneg_left hprob.1 (Real.exp_nonneg
    (-(Cs * ((diskEquilibriumWeightConstant / A) / (2 / Real.pi))) / 2))
  have hfinal := hlo.trans hsig
  simpa only [w, mul_div_assoc] using hfinal

end SRWTightness
