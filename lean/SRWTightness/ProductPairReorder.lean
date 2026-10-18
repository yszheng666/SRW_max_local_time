import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory
namespace SRWTightness

/-- Pair each independent record with its own independent auxiliary variable. -/
theorem product_pair_reorder {α β γ δ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    (μ : Measure α) (ν : Measure β) (σ : Measure γ) (τ : Measure δ)
    [SFinite μ] [SFinite ν] [SFinite σ] [SFinite τ] :
    MeasurePreserving (fun q : (α × β) × (γ × δ) ↦ ((q.1.1, q.2.1), (q.1.2, q.2.2)))
      ((μ.prod ν).prod (σ.prod τ)) ((μ.prod σ).prod (ν.prod τ)) := by
  have h₁ := measurePreserving_prodAssoc μ ν (σ.prod τ)
  have h₂ := (MeasurePreserving.id μ).prod
    (MeasurePreserving.symm MeasurableEquiv.prodAssoc (measurePreserving_prodAssoc ν σ τ))
  have h₃ := (MeasurePreserving.id μ).prod
    ((Measure.measurePreserving_swap (μ := ν) (ν := σ)).prod (MeasurePreserving.id τ))
  have h₄ := (MeasurePreserving.id μ).prod (measurePreserving_prodAssoc σ ν τ)
  have h₅ := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc μ σ (ν.prod τ))
  exact h₅.comp (h₄.comp (h₃.comp (h₂.comp h₁)))

end SRWTightness
