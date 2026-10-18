import SRWTightness.SourceEndpointBridgeConditionalMoment
import SRWTightness.TerminalBridgeMomentWindow

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Earlier increments retain a uniform linear second moment under the full terminal event. -/
theorem terminal_product_conditional_increment (hGaussian : GaussianIntervalInput)
    (hReflection : BridgeReflectionInput) (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (Cm γ : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hIncrement : BesselThreeIncrementInput) (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2) :
    ∃ H₀ : ℝ, 1 ≤ H₀ ∧ ∀ Hmax ε K D : ℝ,
      H₀ ≤ Hmax → 0 ≤ ε → 0 ≤ K → 1 ≤ D →
      ∃ C : ℝ, 0 < C ∧ ∀ H d q At V Δ : ℝ,
      H ∈ Set.Icc H₀ Hmax → 256 * H ≤ d →
      q ∈ Set.Icc (Real.sqrt d) (2 * Real.sqrt d) →
      |At - (2 * d + q)| ≤ ε → |V - d| ≤ K → Δ ∈ Set.Icc 1 D →
      ∀ r s : ℝ, 0 ≤ r → r ≤ s → s ≤ d - H →
      let μ := ((gaussianReal 0 (d - H).toNNReal).prod gaussianCoefficientLaw).prod
        (gaussianReal 0 Δ.toNNReal)
      let E := terminalBridgeProductEvent (d - H) (q - Real.sqrt H - 1)
        (q - Real.sqrt H) At V q d γ
      let f := fun p : (ℝ × GaussianCoefficientSpace) × ℝ ↦
        (endpointBrownianBridge (d - H) p.1.1 s p.1.2 -
          endpointBrownianBridge (d - H) p.1.1 r p.1.2) ^ 2
      Integrable f (ProbabilityTheory.cond μ E) ∧
        (∫ p, f p ∂ProbabilityTheory.cond μ E) ≤ C * (s - r) := by
  obtain ⟨Hi, hHi, hi⟩ := sourceEndpointBridge_conditional_moment hGaussian hReflection
    hBridge hReverse hPositive hInitial hHit Cm hMoment hIncrement γ hγ hγhalf
  obtain ⟨Hp, cp, Cp, hHp, hcp, hCp, hp⟩ := source_endpoint_bridge_probability hGaussian
    hReflection hBridge hReverse hPositive hInitial hHit Cm γ hMoment hγ hγhalf
  refine ⟨max Hi Hp, hHi.trans (le_max_left _ _), ?_⟩
  intro Hmax ε K D hmax hε hK hD
  obtain ⟨cw, hcw, hw⟩ := terminalBridge_conditional_moment_window
    (gaussianIntervalInput_unitWindow hGaussian) (Real.sqrt (max Hi Hp))
    (Real.sqrt Hmax) ε K D (Real.sqrt_le_sqrt hmax) hε hK hD
  refine ⟨cw⁻¹ * (96 * Real.exp 4), by positivity, ?_⟩
  intro H d q At V Δ hH hd hq hAt hV hΔ r s hr hrs hs
  dsimp only
  have hiH := (le_max_left Hi Hp).trans hH.1
  have hpH := (le_max_right Hi Hp).trans hH.1
  have hH0 : 0 < H := by linarith
  have hd0 : 0 < d := by linarith
  have hb := hp H d q hpH hd hq
  have hm := hi H d q hiH hd hq r s hr hrs hs
  have hl := conditional_product_cylinder_moment
    ((gaussianReal 0 (d - H).toNNReal).prod gaussianCoefficientLaw)
    (gaussianReal 0 Δ.toNNReal) _ _ hm.1
  have ht := hw (Real.sqrt H) (d - H) At V d q Δ γ
    ⟨Real.sqrt_le_sqrt hH.1, Real.sqrt_le_sqrt hH.2⟩ hAt hV hΔ
    (lt_of_lt_of_le (by positivity) hb.1) _ hl.1 (fun p ↦ sq_nonneg _)
  refine ⟨ht.1, ?_⟩
  rw [hl.2] at ht
  exact ht.2.trans ((mul_le_mul_of_nonneg_left hm.2 (inv_nonneg.mpr hcw.le)).trans_eq
    (by ring))

end SRWTightness
