import SRWTightness.ConditionalMomentIntegral
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- A probability-weighted event integral bound gives the normalized conditional moment. -/
theorem event_integral_conditional_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (s : Set Ω) (f : Ω → ℝ)
    (hpos : 0 < μ.real s) (hf : Integrable f (μ.restrict s)) (C : ℝ)
    (hC : (∫ ω in s, f ω ∂μ) ≤ C * μ.real s) :
    Integrable f (ProbabilityTheory.cond μ s) ∧
      (∫ ω, f ω ∂ProbabilityTheory.cond μ s) ≤ C := by
  have hs0 : μ s ≠ 0 := by
    intro h
    simp [Measure.real, h] at hpos
  refine ⟨hf.smul_measure (ENNReal.inv_ne_top.mpr hs0), ?_⟩
  rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv]
  change (μ.real s)⁻¹ * (∫ ω in s, f ω ∂μ) ≤ C
  calc
    _ ≤ (μ.real s)⁻¹ * (C * μ.real s) :=
      mul_le_mul_of_nonneg_left hC (inv_nonneg.mpr hpos.le)
    _ = C := by field_simp

/-- Conditioning on a first-coordinate event leaves the independent factor unchanged. -/
theorem conditional_product_cylinder {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (s : Set Ω) :
    ProbabilityTheory.cond (μ.prod ν) (s ×ˢ Set.univ) =
      (ProbabilityTheory.cond μ s).prod ν := by
  unfold ProbabilityTheory.cond
  rw [Measure.prod_prod, measure_univ, mul_one, ← Measure.prod_restrict,
    Measure.restrict_univ, Measure.prod_smul_left]

/-- Independent auxiliary coordinates preserve a conditional first-coordinate moment exactly. -/
theorem conditional_product_cylinder_moment {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (s : Set Ω) (f : Ω → ℝ) (hf : Integrable f (ProbabilityTheory.cond μ s)) :
    Integrable (fun p : Ω × Ξ ↦ f p.1) (ProbabilityTheory.cond (μ.prod ν) (s ×ˢ Set.univ)) ∧
      (∫ p, f p.1 ∂ProbabilityTheory.cond (μ.prod ν) (s ×ˢ Set.univ)) =
        ∫ x, f x ∂ProbabilityTheory.cond μ s := by
  rw [conditional_product_cylinder]
  refine ⟨hf.comp_fst ν, ?_⟩
  rw [integral_fun_fst]
  simp

end SRWTightness
