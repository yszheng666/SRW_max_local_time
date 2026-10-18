import SRWTightness.BridgeConditionalProbability

open MeasureTheory
namespace SRWTightness

/-- Equal measurable path laws give equal full-time crossing probabilities on continuous paths. -/
theorem continuous_crossing_probability_of_path_law {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) (F : ℝ → Ω → ℝ) (G : ℝ → Ξ → ℝ)
    (hF : ∀ t, Measurable (F t)) (hG : ∀ t, Measurable (G t))
    (hcF : ∀ᵐ ω ∂μ, Continuous (fun t ↦ F t ω))
    (hcG : ∀ᵐ ω ∂ν, Continuous (fun t ↦ G t ω))
    (T : ℝ) (bound : ℝ → ℝ) (hb : Continuous bound)
    (he : μ.map (fun ω (u : Set.Icc (0 : ℝ) T) ↦ F u ω) =
      ν.map (fun ω (u : Set.Icc (0 : ℝ) T) ↦ G u ω)) :
    μ.real {ω | ∃ t ∈ Set.Icc (0 : ℝ) T, F t ω < bound t} =
      ν.real {ω | ∃ t ∈ Set.Icc (0 : ℝ) T, G t ω < bound t} := by
  have hm := dyadicLowerPathEvent_measurable T bound
  have heF : {ω | ∃ t ∈ Set.Icc (0 : ℝ) T, F t ω < bound t} =ᵐ[μ]
      (fun ω (u : Set.Icc (0 : ℝ) T) ↦ F u ω) ⁻¹' dyadicLowerPathEvent T bound := by
    filter_upwards [hcF] with ω hω
    exact propext (continuous_crossing_iff_dyadic _ bound hω hb T)
  have heG : {ω | ∃ t ∈ Set.Icc (0 : ℝ) T, G t ω < bound t} =ᵐ[ν]
      (fun ω (u : Set.Icc (0 : ℝ) T) ↦ G u ω) ⁻¹' dyadicLowerPathEvent T bound := by
    filter_upwards [hcG] with ω hω
    exact propext (continuous_crossing_iff_dyadic _ bound hω hb T)
  have hmF : Measurable (fun ω (u : Set.Icc (0 : ℝ) T) ↦ F u ω) :=
    measurable_pi_lambda _ (fun u ↦ hF u)
  have hmG : Measurable (fun ω (u : Set.Icc (0 : ℝ) T) ↦ G u ω) :=
    measurable_pi_lambda _ (fun u ↦ hG u)
  rw [measureReal_congr heF, measureReal_congr heG,
    ← map_measureReal_apply hmF hm, ← map_measureReal_apply hmG hm, he]

end SRWTightness
