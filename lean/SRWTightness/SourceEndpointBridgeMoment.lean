import SRWTightness.SourceBridgeSectionMoment
import SRWTightness.ProductNonnegativeMoment

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Integrating the endpoint window preserves the source bridge increment moment bound. -/
theorem sourceEndpointBridge_moment (hReflection : BridgeReflectionInput)
    (hBridge : PositiveBridgeRestrictionInput) (hReverse : PositiveBridgeReversalInput)
    (hPositive : BesselThreePositiveInput) (hInitial : BesselThreeHittingInput)
    (hHit : BesselThreeDelayedHittingInput) (C : ℝ)
    (hMoment : BesselThreeInverseMomentInput C) (hIncrement : BesselThreeIncrementInput)
    (γ : ℝ) (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2) :
    ∃ H₀ : ℝ, 1 ≤ H₀ ∧ ∀ H d q : ℝ, H₀ ≤ H → 256 * H ≤ d →
      q ∈ Set.Icc (Real.sqrt d) (2 * Real.sqrt d) →
      ∀ r s : ℝ, 0 ≤ r → r ≤ s → s ≤ d - H →
      let μ := (gaussianReal 0 (d - H).toNNReal).prod gaussianCoefficientLaw
      let E := endpointBridgeProductEvent (d - H)
        (q - Real.sqrt H - 1) (q - Real.sqrt H) q d γ
      let f := fun p : ℝ × GaussianCoefficientSpace ↦
        (endpointBrownianBridge (d - H) p.1 s p.2 -
          endpointBrownianBridge (d - H) p.1 r p.2) ^ 2
      Integrable f (μ.restrict E) ∧
        (∫ p in E, f p ∂μ) ≤ (96 * Real.exp 4 * (s - r)) * μ.real E := by
  obtain ⟨H₀, hH₀, hsection⟩ := sourceBridge_section_moment hReflection hBridge hReverse
    hPositive hInitial hHit C hMoment hIncrement γ hγ hγhalf
  refine ⟨H₀, hH₀, ?_⟩
  intro H d q hH hd hq r s hr hrs hs
  let E := endpointBridgeProductEvent (d - H)
    (q - Real.sqrt H - 1) (q - Real.sqrt H) q d γ
  let f := fun p : ℝ × GaussianCoefficientSpace ↦
    (endpointBrownianBridge (d - H) p.1 s p.2 -
      endpointBrownianBridge (d - H) p.1 r p.2) ^ 2
  have hE : MeasurableSet E := endpointBridgeProductEvent_measurable _ _ _ _ _ _
  have hm (v : ℝ) : Measurable (fun p : ℝ × GaussianCoefficientSpace ↦
      endpointBrownianBridge (d - H) p.1 v p.2) :=
    ((actualIntervalBridge_measurable (d - H) v).comp measurable_snd).add
      (measurable_const.mul measurable_fst)
  have hf : StronglyMeasurable f := ((hm s).sub (hm r)).pow_const 2 |>.stronglyMeasurable
  have hg : StronglyMeasurable (E.indicator f) := hf.indicator hE
  have hn : ∀ p, 0 ≤ E.indicator f p := by
    intro p
    by_cases hp : p ∈ E <;> simp [hp, f, sq_nonneg]
  have hh := product_nonnegative_event_moment (gaussianReal 0 (d - H).toNNReal)
    gaussianCoefficientLaw (E.indicator f) hg hn E hE
    (96 * Real.exp 4 * (s - r)) (by positivity) (by
      intro b
      have he : (fun ω ↦ E.indicator f (b, ω)) =
          (Prod.mk b ⁻¹' E).indicator (fun ω ↦ f (b, ω)) := by
        funext ω
        by_cases hb : (b, ω) ∈ E <;> simp [hb]
      rw [he]
      have hme : MeasurableSet (Prod.mk b ⁻¹' E) := hE.preimage measurable_prodMk_left
      by_cases hb : b ∈ Set.Icc (q - Real.sqrt H - 1) (q - Real.sqrt H)
      · have hi := hsection H d q b hH hd hq hb r s hr hrs hs
        refine ⟨(integrable_indicator_iff hme).mpr hi.1, ?_⟩
        rw [integral_indicator hme]
        exact hi.2
      · have hempty : Prod.mk b ⁻¹' E = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro ω hω
          exact hb hω.1
        simp [hempty])
  refine ⟨(integrable_indicator_iff hE).mp hh.1, ?_⟩
  rw [integral_indicator hE] at hh
  exact hh.2

end SRWTightness
