import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- An independent symmetric increment can be reflected while preserving the joint past law. -/
theorem independent_symmetric_reflection {Ω E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → E) (Z : Ω → ℝ) (g : E → ℝ)
    (hX : Measurable X) (hZ : Measurable Z) (hg : Measurable g)
    (hind : IndepFun X Z μ) (hsym : μ.map Z = μ.map (fun ω ↦ -Z ω)) :
    μ.map (fun ω ↦ (X ω, g (X ω) + Z ω)) =
      μ.map (fun ω ↦ (X ω, g (X ω) - Z ω)) := by
  have hn : IndepFun X (fun ω ↦ -Z ω) μ := hind.comp measurable_id measurable_neg
  have hneg : Measurable (fun ω ↦ -Z ω) := hZ.neg
  have hp : μ.map (fun ω ↦ (X ω, Z ω)) = μ.map (fun ω ↦ (X ω, -Z ω)) := by
    rw [hind.map_prod_eq_prod_map_map hX.aemeasurable hZ.aemeasurable,
      hn.map_prod_eq_prod_map_map hX.aemeasurable hneg.aemeasurable, hsym]
  let F : E × ℝ → E × ℝ := fun p ↦ (p.1, g p.1 + p.2)
  have hF : Measurable F := measurable_fst.prodMk ((hg.comp measurable_fst).add measurable_snd)
  have he := congrArg (fun ν : Measure (E × ℝ) ↦ ν.map F) hp
  have hm : Measurable (fun ω ↦ (X ω, -Z ω)) := hX.prodMk hZ.neg
  rw [Measure.map_map hF (hX.prodMk hZ), Measure.map_map hF hm] at he
  simpa only [Function.comp_def, F, sub_eq_add_neg] using he

end SRWTightness
