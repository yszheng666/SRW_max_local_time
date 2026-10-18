import SRWTightness.ExternalGaussianEndpointResidual
import SRWTightness.LocalizedIntervalBridge

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Regrouping independent averages, bridges and residuals preserves their product law. -/
theorem product_swap_last_two {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure β) (κ : Measure γ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure κ] :
    ((μ.prod ν).prod κ).map (fun p ↦ ((p.1.1, p.2), p.1.2)) = (μ.prod κ).prod ν := by
  apply Measure.ext_prod₃_iff'.mpr
  intro s t u hs ht hu
  rw [Measure.map_apply (by fun_prop) ((hs.prod ht).prod hu)]
  have he : (fun p : (α × β) × γ ↦ ((p.1.1, p.2), p.1.2)) ⁻¹'
      ((s ×ˢ t) ×ˢ u) = (s ×ˢ u) ×ˢ t := by
    ext p
    simp only [Set.mem_preimage, Set.mem_prod]
    tauto
  rw [he]
  simp only [Measure.prod_prod]
  ring

noncomputable def pairResidualCoordinates {n : ℕ} (last : Fin n)
    (p : (Fin n → ℝ) × (Fin 2 → ℝ)) : PairObservationIndex n → ℝ :=
  fun j ↦ match j with
    | Sum.inl a => p.1 a
    | Sum.inr c => p.1 last + p.2 (if c then 1 else 0)

theorem pairResidualCoordinates_measurable {n : ℕ} (last : Fin n) :
    Measurable (pairResidualCoordinates last) := by
  apply measurable_pi_iff.mpr
  intro j
  cases j <;> simp only [pairResidualCoordinates] <;> fun_prop

/-- The finite endpoint-residual law includes independent auxiliary bridges with their exact order. -/
theorem pair_residual_auxiliary_law {n : ℕ} (last : Fin n)
    (μ : Measure (Fin n → ℝ)) (κ : Measure (Fin 2 → ℝ))
    (ν : Measure (ℕ → GaussianCoefficientSpace))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure κ] [IsProbabilityMeasure ν]
    (ρ : Measure (PairObservationIndex n → ℝ))
    (hρ : ρ = (μ.prod κ).map (pairResidualCoordinates last)) :
    ρ.prod ν = ((μ.prod ν).prod κ).map
      (fun p ↦ (pairResidualCoordinates last (p.1.1, p.2), p.1.2)) := by
  have hmap := Measure.map_prod_map (μ.prod κ) ν
    (pairResidualCoordinates_measurable last) measurable_id
  rw [Measure.map_id] at hmap
  calc
    ρ.prod ν = ((μ.prod κ).prod ν).map
        (fun p ↦ (pairResidualCoordinates last p.1, p.2)) := by
      rw [hρ]
      exact hmap
    _ = (((μ.prod ν).prod κ).map (fun p ↦ ((p.1.1, p.2), p.1.2))).map
        (fun p ↦ (pairResidualCoordinates last p.1, p.2)) := by
      rw [product_swap_last_two μ ν κ]
    _ = _ := by
      have hm : Measurable (fun p : ((Fin n → ℝ) × (Fin 2 → ℝ)) ×
          (ℕ → GaussianCoefficientSpace) ↦ (pairResidualCoordinates last p.1, p.2)) :=
        ((pairResidualCoordinates_measurable last).comp measurable_fst).prodMk measurable_snd
      rw [Measure.map_map hm (by fun_prop)]
      rfl

end SRWTightness
