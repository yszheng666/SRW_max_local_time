import SRWTightness.ConditionalMomentWindow
import SRWTightness.TerminalProductUniformProbability

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Adding the final site window preserves nonnegative conditional moments with one uniform factor. -/
theorem terminalBridge_conditional_moment_window (hWindow : GaussianUnitWindowInput)
    (aL aU ε K D : ℝ) (ha : aL ≤ aU) (hε : 0 ≤ ε) (hK : 0 ≤ K) (hD : 1 ≤ D) :
    ∃ c : ℝ, 0 < c ∧ ∀ a T At V d q Δ γ : ℝ,
      a ∈ Set.Icc aL aU → |At - (2 * d + q)| ≤ ε → |V - d| ≤ K → Δ ∈ Set.Icc 1 D →
      let μ := (gaussianReal 0 T.toNNReal).prod gaussianCoefficientLaw
      let ρ := μ.prod (gaussianReal 0 Δ.toNNReal)
      let E := endpointBridgeProductEvent T (q - a - 1) (q - a) q d γ
      let F := terminalBridgeProductEvent T (q - a - 1) (q - a) At V q d γ
      0 < μ.real E → ∀ f : ((ℝ × GaussianCoefficientSpace) × ℝ) → ℝ,
      Integrable f (ProbabilityTheory.cond ρ (E ×ˢ Set.univ)) → (∀ p, 0 ≤ f p) →
      Integrable f (ProbabilityTheory.cond ρ F) ∧
        (∫ p, f p ∂ProbabilityTheory.cond ρ F) ≤
          c⁻¹ * ∫ p, f p ∂ProbabilityTheory.cond ρ (E ×ˢ Set.univ) := by
  obtain ⟨c, hc, hw⟩ := terminalBridge_product_probability_uniform hWindow aL aU ε K D
    ha hε hK hD
  refine ⟨c, hc, ?_⟩
  intro a T At V d q Δ γ ha' hAt hV hΔ
  dsimp only
  intro hpos f hf hn
  have hp := hw a T At V d q Δ γ ha' hAt hV hΔ
  dsimp only at hp
  have he : ((((gaussianReal 0 T.toNNReal).prod gaussianCoefficientLaw).prod
      (gaussianReal 0 Δ.toNNReal)).real
      (endpointBridgeProductEvent T (q - a - 1) (q - a) q d γ ×ˢ Set.univ)) =
      ((gaussianReal 0 T.toNNReal).prod gaussianCoefficientLaw).real
        (endpointBridgeProductEvent T (q - a - 1) (q - a) q d γ) := by
    simp only [measureReal_prod_prod, measureReal_univ_eq_one, mul_one]
  apply conditional_nonnegative_moment_relative _ _ _ f
    ((endpointBridgeProductEvent_measurable _ _ _ _ _ _).prod MeasurableSet.univ).nullMeasurableSet
    (by simpa only [he] using hpos)
    (fun p hp ↦ ⟨hp.1, Set.mem_univ _⟩) c hc _ hf hn
  simpa only [he] using hp.1

end SRWTightness
