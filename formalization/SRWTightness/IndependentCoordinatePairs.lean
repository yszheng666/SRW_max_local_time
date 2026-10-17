import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.HasLaw

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Independent coordinate pairs remain independent after collecting their first and second
parts. -/
theorem independent_coordinate_pairs {ι Ω α β : Type*} [Fintype ι]
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → α) (g : Ω → β)
    (hf : Measurable f) (hg : Measurable g) (hfg : IndepFun f g μ) :
    IndepFun (fun ω : ι → Ω ↦ fun i ↦ f (ω i))
      (fun ω : ι → Ω ↦ fun i ↦ g (ω i)) (Measure.infinitePi (fun _ : ι ↦ μ)) := by
  letI : IsProbabilityMeasure (μ.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  letI : IsProbabilityMeasure (μ.map g) := Measure.isProbabilityMeasure_map hg.aemeasurable
  have hlF : HasLaw f (μ.map f) μ := ⟨hf.aemeasurable, rfl⟩
  have hlG : HasLaw g (μ.map g) μ := ⟨hg.aemeasurable, rfl⟩
  have hlFG := hfg.hasLaw_prod hlF hlG
  have he (i : ι) := (measurePreserving_eval_infinitePi (fun _ : ι ↦ μ) i).hasLaw
  have hF := (iIndepFun_infinitePi (fun _ : ι ↦ hf)).hasLaw_pi
    (fun i ↦ hlF.comp (he i))
  have hG := (iIndepFun_infinitePi (fun _ : ι ↦ hg)).hasLaw_pi
    (fun i ↦ hlG.comp (he i))
  have hFG := (iIndepFun_infinitePi (fun _ : ι ↦ hf.prodMk hg)).hasLaw_pi
    (fun i ↦ hlFG.comp (he i))
  have heq := (measurePreserving_arrowProdEquivProdArrow α β ι
    (fun _ ↦ μ.map f) (fun _ ↦ μ.map g)).hasLaw.comp hFG
  apply (indepFun_iff_hasLaw_prodMk_prod hF hG).mpr
  exact heq

end SRWTightness
