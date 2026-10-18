import SRWTightness.SourceRemainingEvents

open MeasureTheory Filter
namespace SRWTightness

/-- Both original remaining successes, including their terminal bridges, map into the fixed-root
reference event almost surely under the actual exterior-conditioned common law. -/
theorem source_conditional_remaining_event_image (hExt : ExteriorBridgeFactorizationInput)
    (hFlat : TwoLevelWordFlatteningInput) :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w → 1 ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      ∀ (A γ : ℝ) (I₀ I₁ : ℕ)
        (z₀ : translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀)))
        (z₁ : translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))),
      1 ≤ A * diskEnergyGapRatio ^ I₀ →
      A * diskEnergyGapRatio ^ I₀ ≤ sourceLowerRadius t / t ^ 6 →
      ∀ h : ExteriorPathRecord,
      0 < pathLaw.real {ω | sourcePairExteriorRecord t b w ν J ω = h} → ∀ k l : ℕ,
      ∀ᵐ p ∂ProbabilityTheory.cond sourceEnlargedLaw
        {p | sourcePairExteriorRecord t b w ν J p.1 = h},
      p ∈ sourceSiteRemainingSuccessEvent t A γ b I₀ z₀ ν →
      p ∈ sourceSiteRemainingSuccessEvent t A γ w I₁ z₁ ν →
      sourceActualCount t b ν p.1 = k → sourceActualCount t w ν p.1 = l →
      (sourceFineTuple t b w
        (translateFinset b (diskFinset (A * diskEnergyGapRatio ^ I₀)))
        (translateFinset w (diskFinset (A * diskEnergyGapRatio ^ I₁))) ν J h p.1,
          (p.2 b, p.2 w)) ∈ sourceTaggedRemainingEvent t A γ b w I₀ I₁ ν z₀ z₁ h k l := by
  filter_upwards [source_conditional_fine_tuple_actual_forests hExt hFlat] with t ht
  intro b w ν J hb hw hbw hd hν hform A γ I₀ I₁ z₀ z₁ ha hc h hh k l
  filter_upwards [ht b w ν J hb hw hbw hd hν hform _ _
    (A * diskEnergyGapRatio ^ I₀) ha hc h hh] with p hp
  intro hs₀ hs₁ hx hy
  change (_, p.2 b) ∈ sourceContinuationForestEvent _ _ _ _ _ _ _ _
    (sourceActualCount t b ν p.1) at hs₀
  change (_, p.2 w) ∈ sourceContinuationForestEvent _ _ _ _ _ _ _ _
    (sourceActualCount t w ν p.1) at hs₁
  rw [hx] at hs₀
  rw [hy] at hs₁
  change ((orderedTaggedForests _).1, p.2 b) ∈ _ ∧
    ((orderedTaggedForests _).2, p.2 w) ∈ _
  rw [hp.2.1]
  exact ⟨hs₀, hs₁⟩

end SRWTightness
