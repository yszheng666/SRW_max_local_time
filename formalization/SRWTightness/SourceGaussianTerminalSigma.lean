import SRWTightness.GaussianGridTerminalSigmaUniform
import SRWTightness.SourceGaussianErrorBounds

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The actual source grid satisfies the terminal covariance comparison with a uniform error cost. -/
theorem sourceGaussian_terminal_sigma_lower (hReconstruct : BrownianBridgeReconstructionInput)
    (hGaussian : GaussianIntervalInput)
    (hReflection : BridgeReflectionInput) (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (Cm γ : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hIncrement : BesselThreeIncrementInput) (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2) :
    ∃ H₀ : ℝ, 1 ≤ H₀ ∧ ∀ Hmax ε K D : ℝ,
      H₀ ≤ Hmax → 0 ≤ ε → 0 ≤ K → 1 ≤ D →
      ∃ C : ℝ, 0 < C ∧ ∀ (b : Site) (t A : ℝ),
      diskPointGaussianMinimumRadius ≤ A → sourceGaussianThreshold A ≤ t →
      ∀ I : ℕ,
      (∀ i : ℕ, A * diskEnergyGapRatio ^ i ≤ sourceLowerRadius t / t ^ 6 ↔ i ≤ I) →
      ∀ d q At V : ℝ,
      let T := sourceObservationTime t A I
      let H := d - T (I + 1)
      let Δ := T ((I + 1) + 1) - T (I + 1)
      H ∈ Set.Icc H₀ Hmax → 256 * H ≤ d →
      q ∈ Set.Icc (Real.sqrt d) (2 * Real.sqrt d) →
      |At - (2 * d + q)| ≤ ε → |V - d| ≤ K → Δ ∈ Set.Icc 1 D →
      let e := geometricDiskPointError b A (Real.exp 1 * sourceLowerRadius t + 14)
        diskEnergyGapRatio (2 / Real.pi) (I + 1)
      let Kmat := brownianTimeMatrix T ((I + 1) + 1)
      let μ := (gaussianCoordinateLaw Kmat).prod (independentBridgeLaw ℕ)
      let E := gaussianGridTerminalEvent T (I + 1) (q - Real.sqrt H - 1)
        (q - Real.sqrt H) At V q d γ
      Real.exp (-(C * ((diskEquilibriumWeightConstant / A) / (2 / Real.pi))) / 2) * μ.real E ≤
        ((gaussianCoordinateLaw (Kmat - Matrix.diagonal e)).prod
          (independentBridgeLaw ℕ)).real E := by
  obtain ⟨H₀, hH₀, hp⟩ := gaussianGrid_terminal_sigma_lower_uniform hReconstruct hGaussian
    hReflection hBridge hReverse hPositive hInitial hHit Cm γ hMoment hIncrement hγ hγhalf
  refine ⟨H₀, hH₀, ?_⟩
  intro Hmax ε K D hmax hε hK hD
  obtain ⟨C, hC, hc⟩ := hp Hmax ε K D hmax hε hK hD
  refine ⟨C, hC, ?_⟩
  intro b t A hA ht I hI d q At V
  dsimp only
  intro hH hd hq hAt hV hΔ
  have he := source_gaussian_error_bounds b t A hA ht I hI
  have hh := hc (sourceObservationTime t A I) I (sourceObservationTime_zero t A I)
    (sourceObservationTime_gaps t A hA ht I hI) d q At V hH hd hq hAt hV hΔ
    (geometricDiskPointError b A (Real.exp 1 * sourceLowerRadius t + 14)
      diskEnergyGapRatio (2 / Real.pi) (I + 1)) he.1 he.2.2
  apply le_trans _ hh
  apply mul_le_mul_of_nonneg_right _ (measureReal_nonneg)
  apply Real.exp_le_exp.mpr
  have hb := mul_le_mul_of_nonneg_left he.2.1 hC.le
  linarith

end SRWTightness
