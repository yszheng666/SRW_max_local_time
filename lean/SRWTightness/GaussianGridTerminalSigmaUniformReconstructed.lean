import SRWTightness.GaussianGridTerminalSigmaUniform
import SRWTightness.GaussianGridTerminalIncrementMomentReconstructed
import SRWTightness.GaussianGridTerminalProbabilityReconstructed

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Companion using the proved endpoint/bridge law of the actual measurable Gaussian path. -/
theorem gaussianGrid_terminal_sigma_lower_uniform_reconstructed
    (hGaussian : GaussianIntervalInput)
    (hReflection : BridgeReflectionInput) (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (Cm γ : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hIncrement : BesselThreeIncrementInput) (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2) :
    ∃ H₀ : ℝ, 1 ≤ H₀ ∧ ∀ Hmax ε K D : ℝ,
      H₀ ≤ Hmax → 0 ≤ ε → 0 ≤ K → 1 ≤ D →
      ∃ C : ℝ, 0 < C ∧ ∀ (T : ℕ → ℝ) (n : ℕ), T 0 = 0 →
      (∀ j < (n + 1) + 1, 1 ≤ T (j + 1) - T j) → ∀ d q At V : ℝ,
      let H := d - T (n + 1)
      let Δ := T ((n + 1) + 1) - T (n + 1)
      H ∈ Set.Icc H₀ Hmax → 256 * H ≤ d →
      q ∈ Set.Icc (Real.sqrt d) (2 * Real.sqrt d) →
      |At - (2 * d + q)| ≤ ε → |V - d| ≤ K → Δ ∈ Set.Icc 1 D →
      ∀ e : Fin ((n + 1) + 1) → ℝ, (∀ i, 0 ≤ e i) → (∀ i, e i ≤ 1 / 8) →
      let Kmat := brownianTimeMatrix T ((n + 1) + 1)
      let μ := (gaussianCoordinateLaw Kmat).prod (independentBridgeLaw ℕ)
      let E := gaussianGridTerminalEvent T (n + 1) (q - Real.sqrt H - 1)
        (q - Real.sqrt H) At V q d γ
      Real.exp (-(C * ∑ i, e i) / 2) * μ.real E ≤
        ((gaussianCoordinateLaw (Kmat - Matrix.diagonal e)).prod
          (independentBridgeLaw ℕ)).real E := by
  obtain ⟨Hp, hHp, hp⟩ := gaussianGrid_terminal_probability_uniform_reconstructed hGaussian
    hReflection hBridge hReverse hPositive hInitial hHit Cm γ hMoment hγ hγhalf
  obtain ⟨Hm, hHm, hm⟩ := gaussianGrid_terminal_conditional_increment_reconstructed hGaussian
    hReflection hBridge hReverse hPositive hInitial hHit Cm γ hMoment hIncrement hγ hγhalf
  refine ⟨max Hp Hm, hHp.trans (le_max_left _ _), ?_⟩
  intro Hmax ε K D hmax hε hK hD
  obtain ⟨cp, Cp, hcp, hCp, hp'⟩ := hp Hmax ε K D
    ((le_max_left _ _).trans hmax) hε hK hD
  obtain ⟨Cm', hCm, hm'⟩ := hm Hmax ε K D
    ((le_max_right _ _).trans hmax) hε hK hD
  let B := (Real.sqrt Hmax + 2 + ε + 2 * K) ^ 2
  refine ⟨8 * max Cm' B, mul_pos (by norm_num) (hCm.trans_le (le_max_left _ _)), ?_⟩
  intro T n hT hgap d q At V
  dsimp only
  intro hH hd hq hAt hV hΔ e he hesmall
  have hprob := hp' T (n + 1) (by omega) hT hgap d q At V
    ⟨(le_max_left _ _).trans hH.1, hH.2⟩ hd hq hAt hV hΔ
  have hdpos : 0 < d := by linarith [hH.1, le_max_left Hp Hm]
  have hpos := (div_pos hcp hdpos).trans_le hprob.1
  have hinc := hm' T (n + 1) (by omega) hT hgap d q At V
    ⟨(le_max_right _ _).trans hH.1, hH.2⟩ hd hq hAt hV hΔ
  have hc := gaussianGrid_terminal_sigma_lower T n hT hgap At V d q
    (Real.sqrt (d - T (n + 1))) ε K γ Cm' hε hK hCm.le hAt hV e he hesmall hpos hinc
  apply le_trans _ hc
  apply mul_le_mul_of_nonneg_right _ hpos.le
  apply Real.exp_le_exp.mpr
  have hbound :
      (8 * max Cm' ((|Real.sqrt (d - T (n + 1))| + 2 + ε + 2 * K) ^ 2)) *
        (∑ i, e i) ≤ (8 * max Cm' B) * ∑ i, e i := by
    apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun i _ ↦ he i))
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 8)
    apply max_le_max (le_refl _)
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    have hs := Real.sqrt_le_sqrt hH.2
    have hs0 := Real.sqrt_nonneg (d - T (n + 1))
    dsimp [B]
    nlinarith
  linarith

end SRWTightness
