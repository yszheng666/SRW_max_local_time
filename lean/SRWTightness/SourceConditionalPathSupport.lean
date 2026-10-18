import SRWTightness.ConditionalAlmostSure
import SRWTightness.SourceConditionalPairLaw

open MeasureTheory
namespace SRWTightness

/-- An original path fact on an exterior fiber remains valid after adjoining the common auxiliary
bridges and conditioning on that fiber. -/
theorem source_conditional_path_support (t : ℝ) (b w : Site) (ν J : ℕ)
    (h : ExteriorPathRecord) (P : Sample → Prop)
    (hP : ∀ᵐ ω ∂pathLaw, sourcePairExteriorRecord t b w ν J ω = h → P ω) :
    ∀ᵐ p ∂ProbabilityTheory.cond sourceEnlargedLaw
      {p | sourcePairExteriorRecord t b w ν J p.1 = h}, P p.1 := by
  letI : MeasurableSpace ExteriorPathRecord := ⊤
  letI : MeasurableSingletonClass ExteriorPathRecord := ⟨fun _ ↦ trivial⟩
  have hH : MeasurableSet {p : Sample × (Site → ℕ → GaussianCoefficientSpace) |
      sourcePairExteriorRecord t b w ν J p.1 = h} :=
    ((measurable_killedExteriorRecord _ _ _ _ _).comp measurable_fst)
      (measurableSet_singleton h)
  apply ae_cond_of_ae_imp sourceEnlargedLaw _ hH (fun p ↦ P p.1)
  exact Measure.quasiMeasurePreserving_fst.ae hP

end SRWTightness
