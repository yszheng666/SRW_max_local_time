import SRWTightness.SourceTerminalSigmaProbability
import SRWTightness.GaussianGridTerminalProbabilityReconstructed
import SRWTightness.SourceGaussianTerminalSigmaReconstructed

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Companion using the proved endpoint/bridge law of the actual measurable Gaussian path. -/
theorem source_terminal_sigma_probability_large_with_margin_reconstructed (J : ℝ)
    (hGaussian : GaussianIntervalInput)
    (hReflection : BridgeReflectionInput) (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (Cm γ : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hIncrement : BesselThreeIncrementInput) (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2) :
    ∃ A c C t₀ : ℝ, diskPointGaussianMinimumRadius ≤ A ∧
      J + sourceEquilibriumTimeError + sourceLowerTimeError ≤ Real.log A ∧ 0 < c ∧ 0 < C ∧
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
      c / d ≤ μ.real E ∧ μ.real E ≤ C / d := by
  obtain ⟨Hp, hHp, hp⟩ := gaussianGrid_terminal_probability_uniform_reconstructed hGaussian
    hReflection hBridge hReverse hPositive hInitial hHit Cm γ hMoment hγ hγhalf
  obtain ⟨Hs, hHs, hs⟩ := sourceGaussian_terminal_sigma_lower_reconstructed hGaussian
    hReflection hBridge hReverse hPositive hInitial hHit Cm γ hMoment hIncrement hγ hγhalf
  obtain ⟨A, Hmax, D, t₀, hA, hlog, hmax, hD, ha⟩ :=
    source_terminal_application_conditions_with_log (max (max Hp Hs) J) 1 (by norm_num)
  have hbase : max Hp Hs ≤ Hmax := (le_max_left _ _).trans hmax
  have hmargin : J + sourceEquilibriumTimeError + sourceLowerTimeError ≤ Real.log A := by
    have hJ : J ≤ max (max Hp Hs) J := le_max_right _ _
    linarith
  let K := max 0 (sourcePointEnergyTimeError + sourceLowerTimeError)
  obtain ⟨cp, Cp, hcp, hCp, hb⟩ := hp Hmax 1 K D
    ((le_max_left _ _).trans hbase) (by norm_num) (le_max_left _ _) hD
  obtain ⟨Cs, hCs, hc⟩ := hs Hmax 1 K D
    ((le_max_right _ _).trans hbase) (by norm_num) (le_max_left _ _) hD
  let w := Real.exp (-(Cs * ((diskEquilibriumWeightConstant / A) / (2 / Real.pi))) / 2)
  let u := Real.exp (4 * diskEquilibriumWeightConstant / (A * (2 / Real.pi)))
  refine ⟨A, w * cp, u * Cp, t₀, hA, hmargin, mul_pos (Real.exp_pos _) hcp,
    mul_pos (Real.exp_pos _) hCp, ?_⟩
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
    ⟨((le_max_left Hp Hs).trans (le_max_left (max Hp Hs) J)).trans hh.2.1.1, hh.2.1.2⟩ hh.2.2.1 hq
      hh.2.2.2.2.1
    (hh.2.2.2.2.2.trans (le_max_right _ _))
    (by simpa only [Nat.add_assoc] using hh.2.2.2.1)
  have hsig := hc b t A hA hh.1 I hI
    (sourceLowerTime (sourceLowerRadius t)) q
    (sourceTerminalThreshold t (sourceTerminalRoot t q))
    (sourcePointEnergyTime b (sourceLowerRadius t) 14)
    ⟨((le_max_right Hp Hs).trans (le_max_left (max Hp Hs) J)).trans hh.2.1.1, hh.2.1.2⟩ hh.2.2.1 hq
      hh.2.2.2.2.1
    (hh.2.2.2.2.2.trans (le_max_right _ _))
    (by simpa only [Nat.add_assoc] using hh.2.2.2.1)
  have hlo := mul_le_mul_of_nonneg_left hprob.1 (Real.exp_nonneg
    (-(Cs * ((diskEquilibriumWeightConstant / A) / (2 / Real.pi))) / 2))
  have hfinal := hlo.trans hsig
  constructor
  · simpa only [w, mul_div_assoc] using hfinal
  · have hu := source_gaussian_event_upper b t A hA hh.1 I hI
      (gaussianGridTerminalEvent (sourceObservationTime t A I) (I + 1)
        (q - Real.sqrt (sourceLowerTime (sourceLowerRadius t) -
          sourceObservationTime t A I (I + 1)) - 1)
        (q - Real.sqrt (sourceLowerTime (sourceLowerRadius t) -
          sourceObservationTime t A I (I + 1)))
        (sourceTerminalThreshold t (sourceTerminalRoot t q))
        (sourcePointEnergyTime b (sourceLowerRadius t) 14) q
        (sourceLowerTime (sourceLowerRadius t)) γ)
    have hup := hu.trans (mul_le_mul_of_nonneg_left hprob.2 (Real.exp_nonneg _))
    simpa only [u, mul_div_assoc] using hup

end SRWTightness
