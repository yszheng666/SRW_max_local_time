import SRWTightness.GaussianGridTerminalIncrementMoment
import SRWTightness.GaussianGridTerminalConditionalLawReconstructed

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Companion using the proved endpoint/bridge law of the actual measurable Gaussian path. -/
theorem gaussianGrid_terminal_conditional_increment_reconstructed
    (hGaussian : GaussianIntervalInput)
    (hReflection : BridgeReflectionInput) (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (Cm γ : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hIncrement : BesselThreeIncrementInput) (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2) :
    ∃ H₀ : ℝ, 1 ≤ H₀ ∧ ∀ Hmax ε K D : ℝ,
      H₀ ≤ Hmax → 0 ≤ ε → 0 ≤ K → 1 ≤ D →
      ∃ C : ℝ, 0 < C ∧ ∀ (T : ℕ → ℝ) (n : ℕ), 0 < n → T 0 = 0 →
      (∀ j < n + 1, 1 ≤ T (j + 1) - T j) → ∀ d q At V : ℝ,
      let H := d - T n
      let Δ := T (n + 1) - T n
      H ∈ Set.Icc H₀ Hmax → 256 * H ≤ d →
      q ∈ Set.Icc (Real.sqrt d) (2 * Real.sqrt d) →
      |At - (2 * d + q)| ≤ ε → |V - d| ≤ K → Δ ∈ Set.Icc 1 D →
      ∀ r s : ℝ, 0 ≤ r → r ≤ s → s ≤ T n →
      let μ := (gaussianCoordinateLaw (brownianTimeMatrix T (n + 1))).prod
        (independentBridgeLaw ℕ)
      let E := gaussianGridTerminalEvent T n (q - Real.sqrt H - 1)
        (q - Real.sqrt H) At V q d γ
      let f := fun p ↦ (gaussianGridPath T n p s - gaussianGridPath T n p r) ^ 2
      Integrable f (ProbabilityTheory.cond μ E) ∧
        (∫ p, f p ∂ProbabilityTheory.cond μ E) ≤ C * (s - r) := by
  obtain ⟨H₀, hH₀, hp⟩ := terminal_product_conditional_increment hGaussian hReflection
    hBridge hReverse hPositive hInitial hHit Cm γ hMoment hIncrement hγ hγhalf
  refine ⟨H₀, hH₀, ?_⟩
  intro Hmax ε K D hmax hε hK hD
  obtain ⟨C, hC, hc⟩ := hp Hmax ε K D hmax hε hK hD
  refine ⟨C, hC, ?_⟩
  intro T n hn hT hgap d q At V
  dsimp only
  intro hH hd hq hAt hV hΔ r s hr hrs hs
  have he : d - (d - T n) = T n := by ring
  have hb := hc (d - T n) d q At V (T (n + 1) - T n)
    hH hd hq hAt hV hΔ r s hr hrs (by rwa [he])
  dsimp only at hb
  rw [he] at hb
  let rr : Set.Icc (0 : ℝ) (T n) := ⟨r, hr, hrs.trans hs⟩
  let ss : Set.Icc (0 : ℝ) (T n) := ⟨s, hr.trans hrs, hs⟩
  let f : ((ℝ × (Set.Icc (0 : ℝ) (T n) → ℝ)) × ℝ) → ℝ :=
    fun p ↦ (p.1.2 ss - p.1.2 rr) ^ 2
  have hf : Measurable f :=
    (((measurable_pi_apply ss).comp (measurable_snd.comp measurable_fst)).sub
      ((measurable_pi_apply rr).comp (measurable_snd.comp measurable_fst))).pow_const 2
  have hh := gaussianGrid_terminal_conditional_observable_reconstructed T n hn hT hgap
    (q - Real.sqrt (d - T n) - 1) (q - Real.sqrt (d - T n)) At V q d γ f hf hb.1
  exact ⟨hh.1, hh.2.trans_le hb.2⟩

end SRWTightness
