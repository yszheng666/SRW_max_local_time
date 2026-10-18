import SRWTightness.SourceRemainingEvents
import SRWTightness.ConditionalRestrictedEvent

open MeasureTheory
namespace SRWTightness

/-- The named remaining-success conditional probability is precisely the restricted original
probability appearing in the source aggregation, including the full exterior and count fiber. -/
theorem source_remaining_conditional_probability (t A γ : ℝ) (b w : Site) (I₀ I₁ ν J : ℕ)
    (z₀ : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀)))
    (z₁ : translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁)))
    (h : ExteriorPathRecord) (k l : ℕ) :
    (ProbabilityTheory.cond sourceEnlargedLaw
      {p | sourcePairExteriorRecord t b w ν J p.1 = h}).real
      {p | p ∈ sourceSiteRemainingSuccessEvent t A γ b I₀ z₀ ν ∧
        p ∈ sourceSiteRemainingSuccessEvent t A γ w I₁ z₁ ν ∧
        sourceActualCount t b ν p.1 = k ∧ sourceActualCount t w ν p.1 = l} =
    (sourceEnlargedLaw.restrict
      (sourceSiteRemainingSuccessEvent t A γ b I₀ z₀ ν ∩
        sourceSiteRemainingSuccessEvent t A γ w I₁ z₁ ν)).real
      {p | sourcePairExteriorRecord t b w ν J p.1 = h ∧
        sourceActualCount t b ν p.1 = k ∧ sourceActualCount t w ν p.1 = l} /
      sourceEnlargedLaw.real {p | sourcePairExteriorRecord t b w ν J p.1 = h} := by
  letI : MeasurableSpace ExteriorPathRecord := ⊤
  letI : MeasurableSingletonClass ExteriorPathRecord := ⟨fun _ ↦ trivial⟩
  have hH : MeasurableSet {p : Sample × (Site → ℕ → GaussianCoefficientSpace) |
      sourcePairExteriorRecord t b w ν J p.1 = h} :=
    ((measurable_killedExteriorRecord _ _ _ _ _).comp measurable_fst)
      (measurableSet_singleton h)
  have hC : MeasurableSet {p : Sample × (Site → ℕ → GaussianCoefficientSpace) |
      sourceActualCount t b ν p.1 = k ∧ sourceActualCount t w ν p.1 = l} :=
    (((measurable_sourceActualCount t b ν).comp measurable_fst)
      (measurableSet_singleton k)).inter
        (((measurable_sourceActualCount t w ν).comp measurable_fst)
          (measurableSet_singleton l))
  simpa only [Set.setOf_and, Set.setOf_mem_eq, Set.inter_assoc] using
    conditional_restricted_event_real sourceEnlargedLaw _ _
      (sourceSiteRemainingSuccessEvent t A γ b I₀ z₀ ν ∩
        sourceSiteRemainingSuccessEvent t A γ w I₁ z₁ ν) hH hC

end SRWTightness
