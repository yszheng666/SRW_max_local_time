import SRWTightness.EndpointBridgeProductEvent
import SRWTightness.ProductEventRealBounds

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Add the mean-shifted unit site window to the endpoint and bridge constraints. -/
def terminalBridgeProductEvent (T l u At V q d γ : ℝ) :
    Set ((ℝ × GaussianCoefficientSpace) × ℝ) :=
  {p | p.1 ∈ endpointBridgeProductEvent T l u q d γ ∧
    p.2 ∈ Set.Icc (At - 2 * V - p.1.1) (At - 2 * V - p.1.1 + 1)}

theorem terminalBridgeProductEvent_measurable (T l u At V q d γ : ℝ) :
    MeasurableSet (terminalBridgeProductEvent T l u At V q d γ) := by
  have hf : Measurable (fun p : (ℝ × GaussianCoefficientSpace) × ℝ ↦
      At - 2 * V - p.1.1) := measurable_const.sub (measurable_fst.comp measurable_fst)
  change MeasurableSet {p : (ℝ × GaussianCoefficientSpace) × ℝ | p.1 ∈ endpointBridgeProductEvent T l u q d γ ∧
    At - 2 * V - p.1.1 ≤ p.2 ∧ p.2 ≤ At - 2 * V - p.1.1 + 1}
  simp only [Set.setOf_and]
  exact ((endpointBridgeProductEvent_measurable _ _ _ _ _ _).preimage measurable_fst).inter
    ((measurableSet_le hf measurable_snd).inter
      (measurableSet_le measurable_snd (hf.add measurable_const)))

/-- Inside the base event, the section is precisely the final increment's unit interval. -/
theorem terminalBridgeProductEvent_section (T l u At V q d γ : ℝ)
    (p : ℝ × GaussianCoefficientSpace) (hp : p ∈ endpointBridgeProductEvent T l u q d γ) :
    Prod.mk p ⁻¹' terminalBridgeProductEvent T l u At V q d γ =
      Set.Icc (At - 2 * V - p.1) (At - 2 * V - p.1 + 1) := by
  ext z
  change (p ∈ endpointBridgeProductEvent T l u q d γ ∧ z ∈ _) ↔ z ∈ _
  exact and_iff_right hp

/-- The independent final site window costs only a fixed positive factor on the source base event. -/
theorem terminalBridge_product_probability (hWindow : GaussianUnitWindowInput)
    (a ε K D : ℝ) (hε : 0 ≤ ε) (hK : 0 ≤ K) (hD : 1 ≤ D) :
    ∃ c : ℝ, 0 < c ∧ ∀ T At V d q Δ γ : ℝ,
      |At - (2 * d + q)| ≤ ε → |V - d| ≤ K → Δ ∈ Set.Icc 1 D →
      let μ := (gaussianReal 0 T.toNNReal).prod gaussianCoefficientLaw
      let E := endpointBridgeProductEvent T (q - a - 1) (q - a) q d γ
      c * μ.real E ≤ (μ.prod (gaussianReal 0 Δ.toNNReal)).real
        (terminalBridgeProductEvent T (q - a - 1) (q - a) At V q d γ) ∧
      (μ.prod (gaussianReal 0 Δ.toNNReal)).real
        (terminalBridgeProductEvent T (q - a - 1) (q - a) At V q d γ) ≤ μ.real E := by
  obtain ⟨c, hc, hw⟩ := source_final_window_probability hWindow a ε K D hε hK hD
  refine ⟨c, hc, ?_⟩
  intro T At V d q Δ γ hAt hV hΔ
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
      exact hw At V d q p.1 Δ hAt hV hp.1 hΔ)
  simpa only [one_mul] using hh

end SRWTightness
