import SRWTightness.TerminalProductUniformProbability
import SRWTightness.GaussianGridTerminalEventLaw

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Uniform terminal probability bounds for the actual Gaussian grid law. -/
theorem gaussianGrid_terminal_probability_uniform (hReconstruct : BrownianBridgeReconstructionInput)
    (hGaussian : GaussianIntervalInput)
    (hReflection : BridgeReflectionInput) (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (Cm γ : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2) :
    ∃ H₀ : ℝ, 1 ≤ H₀ ∧ ∀ Hmax ε K D : ℝ, H₀ ≤ Hmax → 0 ≤ ε → 0 ≤ K → 1 ≤ D →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (T : ℕ → ℝ) (n : ℕ), 0 < n → T 0 = 0 →
      (∀ j < n + 1, 1 ≤ T (j + 1) - T j) → ∀ d q At V : ℝ,
      let H := d - T n
      let Δ := T (n + 1) - T n
      H ∈ Set.Icc H₀ Hmax → 256 * H ≤ d →
      q ∈ Set.Icc (Real.sqrt d) (2 * Real.sqrt d) →
      |At - (2 * d + q)| ≤ ε → |V - d| ≤ K → Δ ∈ Set.Icc 1 D →
      let μ := (gaussianCoordinateLaw (brownianTimeMatrix T (n + 1))).prod
        (independentBridgeLaw ℕ)
      let E := gaussianGridTerminalEvent T n (q - Real.sqrt H - 1)
        (q - Real.sqrt H) At V q d γ
      c / d ≤ μ.real E ∧ μ.real E ≤ C / d := by
  obtain ⟨H₀, hH₀, hp⟩ := terminal_product_probability_uniform hGaussian hReflection
    hBridge hReverse hPositive hInitial hHit Cm γ hMoment hγ hγhalf
  refine ⟨H₀, hH₀, ?_⟩
  intro Hmax ε K D hmax hε hK hD
  obtain ⟨c, C, hc, hC, hb⟩ := hp Hmax ε K D hmax hε hK hD
  refine ⟨c, C, hc, hC, ?_⟩
  intro T n hn hT hgap d q At V
  dsimp only
  intro hH hd hq hAt hV hΔ
  have hh := hb (d - T n) d q At V (T (n + 1) - T n) hH hd hq hAt hV hΔ
  dsimp only at hh
  have ht : d - (d - T n) = T n := by ring
  rw [ht] at hh
  rw [gaussianGrid_terminal_event_probability hReconstruct T n hn hT hgap]
  exact hh

end SRWTightness
