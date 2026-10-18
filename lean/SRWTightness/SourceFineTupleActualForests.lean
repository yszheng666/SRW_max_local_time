import SRWTightness.SourceFineTupleSupport
import SRWTightness.SourceGroupedFineCount

open MeasureTheory Filter
namespace SRWTightness

/-- The fixed fine tuple reconstructs the original two forests and their original root counts.
This identification requires no success event before the splitting level. -/
theorem source_fine_tuple_actual_forests (hExt : ExteriorBridgeFactorizationInput)
    (hFlat : TwoLevelWordFlatteningInput) :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w → 1 ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      ∀ (K₀ K₁ : Finset Site) (a : ℝ), 1 ≤ a → a ≤ sourceLowerRadius t / t ^ 6 →
      ∀ h : ExteriorPathRecord,
      0 < pathLaw.real {ω | sourcePairExteriorRecord t b w ν J ω = h} →
      ∀ᵐ ω ∂pathLaw, sourcePairExteriorRecord t b w ν J ω = h →
        let r := sourceFineTuple t b w K₀ K₁ ν J h ω
        orderedTaggedCompatible (fun i ↦ (h.1.get i).2.1) r ∧
        orderedTaggedForests r =
          (sourceActualFineForest t b K₀ ν ω, sourceActualFineForest t w K₁ ν ω) ∧
        (orderedTaggedForests r).1.length = sourceActualCount t b ν ω ∧
        (orderedTaggedForests r).2.length = sourceActualCount t w ν ω := by
  filter_upwards [source_fine_tuple_support hExt,
    source_grouped_fine_error hFlat 0 0 le_rfl le_rfl,
    source_grouped_fine_count hFlat] with t hsupp hforest hcount
  intro b w ν J hb hw hbw hd hν hform K₀ K₁ a ha hacut h hh
  filter_upwards [hsupp b w ν J hb hw hbw hd hν hform K₀ K₁ h hh,
    hforest b w ν J hb hw hbw hd hν hform b (Or.inl rfl) K₀ a ha hacut,
    hforest b w ν J hb hw hbw hd hν hform w (Or.inr rfl) K₁ a ha hacut,
    hcount b w ν J hb hw hbw hd hν hform b (Or.inl rfl) K₀,
    hcount b w ν J hb hw hbw hd hν hform w (Or.inr rfl) K₁]
    with ω hs hf₀ hf₁ hc₀ hc₁
  intro hω
  obtain ⟨hcompat, hpair⟩ := hs hω
  dsimp only
  refine ⟨hcompat, ?_, ?_, ?_⟩
  · exact hpair.trans (Prod.ext hf₀.1.symm hf₁.1.symm)
  · exact (congrArg (fun p ↦ p.1.length) hpair).trans hc₀
  · exact (congrArg (fun p ↦ p.2.length) hpair).trans hc₁

end SRWTightness
