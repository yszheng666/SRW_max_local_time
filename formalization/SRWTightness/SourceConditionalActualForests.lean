import SRWTightness.SourceFineTupleActualForests
import SRWTightness.SourceConditionalPathSupport

open MeasureTheory Filter
namespace SRWTightness

/-- Under the actual conditional common-space law, the tuple forests and original root counts
agree almost surely, retaining their original dependence. -/
theorem source_conditional_fine_tuple_actual_forests (hExt : ExteriorBridgeFactorizationInput)
    (hFlat : TwoLevelWordFlatteningInput) :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w → 1 ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      ∀ (K₀ K₁ : Finset Site) (a : ℝ), 1 ≤ a → a ≤ sourceLowerRadius t / t ^ 6 →
      ∀ h : ExteriorPathRecord,
      0 < pathLaw.real {ω | sourcePairExteriorRecord t b w ν J ω = h} →
      ∀ᵐ p ∂ProbabilityTheory.cond sourceEnlargedLaw
        {p | sourcePairExteriorRecord t b w ν J p.1 = h},
        let r := sourceFineTuple t b w K₀ K₁ ν J h p.1
        orderedTaggedCompatible (fun i ↦ (h.1.get i).2.1) r ∧
        orderedTaggedForests r =
          (sourceActualFineForest t b K₀ ν p.1, sourceActualFineForest t w K₁ ν p.1) ∧
        (orderedTaggedForests r).1.length = sourceActualCount t b ν p.1 ∧
        (orderedTaggedForests r).2.length = sourceActualCount t w ν p.1 := by
  filter_upwards [source_fine_tuple_actual_forests hExt hFlat] with t ht
  intro b w ν J hb hw hbw hd hν hform K₀ K₁ a ha hacut h hh
  exact source_conditional_path_support t b w ν J h _
    (ht b w ν J hb hw hbw hd hν hform K₀ K₁ a ha hacut h hh)

end SRWTightness
