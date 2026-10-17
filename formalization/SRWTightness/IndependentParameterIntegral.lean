import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Independent noise can be integrated out on every measurable event determined by the
parameter. -/
theorem independent_parameter_setIntegral {Ω α β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure β) [IsProbabilityMeasure ν]
    (X : Ω → α) (Y : Ω → β) (hX : Measurable X) (hY : Measurable Y)
    (hlY : HasLaw Y ν μ) (hind : IndepFun X Y μ)
    (F : α × β → ℝ) (hF : Measurable F)
    (hi : Integrable (fun ω ↦ F (X ω, Y ω)) μ)
    (A : Set α) (hA : MeasurableSet A) :
    (∫ ω in X ⁻¹' A, F (X ω, Y ω) ∂μ) =
      ∫ ω in X ⁻¹' A, ∫ y, F (X ω, y) ∂ν ∂μ := by
  let P : Ω → α × β := fun ω ↦ (X ω, Y ω)
  have hP : Measurable P := hX.prodMk hY
  have hl : μ.map P = (μ.map X).prod ν := by
    rw [hind.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable, hlY.map_eq]
  have hIP : Integrable F ((μ.map X).prod ν) := by
    rw [← hl]
    exact (integrable_map_measure hF.aestronglyMeasurable hP.aemeasurable).mpr hi
  have hJ : StronglyMeasurable (fun a ↦ ∫ y, F (a, y) ∂ν) :=
    hF.stronglyMeasurable.integral_prod_right'
  have hpre : P ⁻¹' (A ×ˢ Set.univ) = X ⁻¹' A := by ext ω; simp [P]
  calc
    _ = ∫ p in A ×ˢ Set.univ, F p ∂μ.map P := by
      rw [setIntegral_map (hA.prod MeasurableSet.univ) hF.aestronglyMeasurable
        hP.aemeasurable, hpre]
    _ = ∫ a in A, ∫ y, F (a, y) ∂ν ∂μ.map X := by
      rw [hl, setIntegral_prod F hIP.integrableOn]
      simp only [setIntegral_univ]
    _ = _ := setIntegral_map hA hJ.aestronglyMeasurable hX.aemeasurable

end SRWTightness
