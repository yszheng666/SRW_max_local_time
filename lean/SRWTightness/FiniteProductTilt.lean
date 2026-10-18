import SRWTightness.FiniteProductDensity
import Mathlib.MeasureTheory.Measure.Tilted

open MeasureTheory

namespace SRWTightness

/-- A sum of separate tilts preserves the finite product measure structure. -/
theorem finite_product_tilt {ι E : Type*} [Fintype ι] [MeasurableSpace E]
    (μ : ι → Measure E) [∀ i, IsProbabilityMeasure (μ i)] (f : ι → E → ℝ)
    (hf : ∀ i, Measurable (f i))
    (hi : ∀ i, Integrable (fun x ↦ Real.exp (f i x)) (μ i)) :
    (Measure.pi μ).tilted (fun x ↦ ∑ i, f i (x i)) =
      Measure.pi (fun i ↦ (μ i).tilted (f i)) := by
  let Z := fun i ↦ ∫ x, Real.exp (f i x) ∂μ i
  let d := fun i x ↦ ENNReal.ofReal (Real.exp (f i x) / Z i)
  letI (i : ι) : IsProbabilityMeasure ((μ i).tilted (f i)) := isProbabilityMeasure_tilted (hi i)
  letI (i : ι) : SigmaFinite ((μ i).withDensity (d i)) :=
    inferInstanceAs (SigmaFinite ((μ i).tilted (f i)))
  have hd (i : ι) : Measurable (d i) := by dsimp [d]; fun_prop
  have hprod := finite_product_withDensity μ d hd
  have hnorm : (∫ x, Real.exp (∑ i, f i (x i)) ∂Measure.pi μ) = ∏ i, Z i := by
    simp_rw [Real.exp_sum]
    exact integral_fintype_prod_eq_prod (fun i x ↦ Real.exp (f i x))
  change (Measure.pi μ).withDensity
    (fun x ↦ ENNReal.ofReal (Real.exp (∑ i, f i (x i)) /
      (∫ x, Real.exp (∑ i, f i (x i)) ∂Measure.pi μ))) =
    Measure.pi (fun i ↦ (μ i).withDensity (d i))
  rw [hprod]
  congr 1
  funext x
  rw [hnorm, Real.exp_sum, ← Finset.prod_div_distrib]
  exact ENNReal.ofReal_prod_of_nonneg (fun i _ ↦
    div_nonneg (Real.exp_pos _).le (integral_exp_pos (hi i)).le)

end SRWTightness
