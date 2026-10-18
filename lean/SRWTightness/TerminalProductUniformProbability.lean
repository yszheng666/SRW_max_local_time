import SRWTightness.TerminalProductProbability

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The final window cost is uniform when the source endpoint offset varies in a fixed interval. -/
theorem terminalBridge_product_probability_uniform (hWindow : GaussianUnitWindowInput)
    (aL aU ε K D : ℝ) (ha : aL ≤ aU) (hε : 0 ≤ ε) (hK : 0 ≤ K) (hD : 1 ≤ D) :
    ∃ c : ℝ, 0 < c ∧ ∀ a T At V d q Δ γ : ℝ,
      a ∈ Set.Icc aL aU → |At - (2 * d + q)| ≤ ε → |V - d| ≤ K → Δ ∈ Set.Icc 1 D →
      let μ := (gaussianReal 0 T.toNNReal).prod gaussianCoefficientLaw
      let E := endpointBridgeProductEvent T (q - a - 1) (q - a) q d γ
      c * μ.real E ≤ (μ.prod (gaussianReal 0 Δ.toNNReal)).real
        (terminalBridgeProductEvent T (q - a - 1) (q - a) At V q d γ) ∧
      (μ.prod (gaussianReal 0 Δ.toNNReal)).real
        (terminalBridgeProductEvent T (q - a - 1) (q - a) At V q d γ) ≤ μ.real E := by
  obtain ⟨c, hc, hw⟩ := hWindow (aL - ε - 2 * K) (aU + 1 + ε + 2 * K)
    1 D (by linarith) (by norm_num) hD
  refine ⟨c, hc, ?_⟩
  intro a T At V d q Δ γ ha' hAt hV hΔ
  dsimp only
  have hh := product_event_real_bounds
    ((gaussianReal 0 T.toNNReal).prod gaussianCoefficientLaw) (gaussianReal 0 Δ.toNNReal)
    (endpointBridgeProductEvent T (q - a - 1) (q - a) q d γ)
    (terminalBridgeProductEvent T (q - a - 1) (q - a) At V q d γ) c 1 hc.le (by norm_num)
    (endpointBridgeProductEvent_measurable _ _ _ _ _ _)
    (terminalBridgeProductEvent_measurable _ _ _ _ _ _ _ _) (by
      intro p hp
      exact ⟨hp.1, Set.mem_univ _⟩) (by
      intro p hp
      rw [terminalBridgeProductEvent_section _ _ _ _ _ _ _ _ p hp]
      have hz := source_site_increment_window_location At V d q a p.1 ε K hAt hV hp.1
      refine ⟨hw _ _ ⟨?_, ?_⟩ hΔ, measureReal_le_one⟩
      · linarith [hz.1, ha'.1]
      · linarith [hz.2, ha'.2])
  simpa only [one_mul] using hh

/-- The complete terminal product bound is uniform over the whole permitted cutoff range. -/
theorem terminal_product_probability_uniform (hGaussian : GaussianIntervalInput)
    (hReflection : BridgeReflectionInput) (hBridge : PositiveBridgeRestrictionInput)
    (hReverse : PositiveBridgeReversalInput) (hPositive : BesselThreePositiveInput)
    (hInitial : BesselThreeHittingInput) (hHit : BesselThreeDelayedHittingInput)
    (Cm γ : ℝ) (hMoment : BesselThreeInverseMomentInput Cm)
    (hγ : 0 ≤ γ) (hγhalf : γ < 1 / 2) :
    ∃ H₀ : ℝ, 1 ≤ H₀ ∧ ∀ Hmax ε K D : ℝ, H₀ ≤ Hmax → 0 ≤ ε → 0 ≤ K → 1 ≤ D →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ H d q At V Δ : ℝ,
      H ∈ Set.Icc H₀ Hmax → 256 * H ≤ d →
      q ∈ Set.Icc (Real.sqrt d) (2 * Real.sqrt d) →
      |At - (2 * d + q)| ≤ ε → |V - d| ≤ K → Δ ∈ Set.Icc 1 D →
      let μ := ((gaussianReal 0 (d - H).toNNReal).prod gaussianCoefficientLaw).prod
        (gaussianReal 0 Δ.toNNReal)
      let E := terminalBridgeProductEvent (d - H) (q - Real.sqrt H - 1)
        (q - Real.sqrt H) At V q d γ
      c / d ≤ μ.real E ∧ μ.real E ≤ C / d := by
  obtain ⟨H₀, cb, Cb, hH₀, hcb, hCb, hb⟩ := source_endpoint_bridge_probability hGaussian
    hReflection hBridge hReverse hPositive hInitial hHit Cm γ hMoment hγ hγhalf
  refine ⟨H₀, hH₀, ?_⟩
  intro Hmax ε K D hmax hε hK hD
  obtain ⟨cw, hcw, hw⟩ := terminalBridge_product_probability_uniform
    (gaussianIntervalInput_unitWindow hGaussian) (Real.sqrt H₀) (Real.sqrt Hmax)
    ε K D (Real.sqrt_le_sqrt hmax) hε hK hD
  have hr0 : 0 < Real.sqrt H₀ := Real.sqrt_pos.mpr (by linarith)
  have hrmax : 0 < Real.sqrt Hmax := hr0.trans_le (Real.sqrt_le_sqrt hmax)
  refine ⟨cw * cb * Real.sqrt H₀, Cb * Real.sqrt Hmax, by positivity, by positivity, ?_⟩
  intro H d q At V Δ hH hd hq hAt hV hΔ
  dsimp only
  have hd0 : 0 < d := by linarith [hH.1]
  have hb' := hb H d q hH.1 hd hq
  have hw' := hw (Real.sqrt H) (d - H) At V d q Δ γ
    ⟨Real.sqrt_le_sqrt hH.1, Real.sqrt_le_sqrt hH.2⟩ hAt hV hΔ
  constructor
  · calc
      _ = cw * (cb * Real.sqrt H₀ / d) := by ring
      _ ≤ cw * (cb * Real.sqrt H / d) := by
        apply mul_le_mul_of_nonneg_left _ hcw.le
        apply div_le_div_of_nonneg_right _ hd0.le
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hH.1) hcb.le
      _ ≤ _ := mul_le_mul_of_nonneg_left hb'.1 hcw.le
      _ ≤ _ := hw'.1
  · apply hw'.2.trans (hb'.2.trans _)
    apply div_le_div_of_nonneg_right _ hd0.le
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hH.2) hCb.le

end SRWTightness
