import SRWTightness.SourceConditionalFineTuple
import SRWTightness.SourceConditionalPathMap

open MeasureTheory
namespace SRWTightness

/-- The actual indexed source fine records inside the fixed exterior header. -/
noncomputable def sourceFineTuple (t : ℝ) (b w : Site) (K₀ K₁ : Finset Site)
    (ν J : ℕ) (h : ExteriorPathRecord) (ω : Sample) :
    Fin h.1.length → SourceExteriorFineValue t K₀ K₁ ν :=
  let m := sourceLowerRadius t
  let ℓ := sourceRootDepth (Real.exp t) m
  let K := fun z ↦ sourceEntranceDomain m 1 ℓ z ν
  let D := fun z ↦ sourceExitDomain m 1 ℓ z (ν - J)
  exteriorFixedTuple h (sourceExteriorFineRecord t b w K₀ K₁ ν)
    (killedChildRecords (diskFinset (Real.exp t)) (K b ∪ K w) (D b ∪ D w)
      0 (fun _ u ↦ u) ω)

/-- Reading the actual fine tuple is measurable for any measurable record codomains. -/
theorem measurable_sourceFineTuple (t : ℝ) (b w : Site) (K₀ K₁ : Finset Site)
    (ν J : ℕ) (h : ExteriorPathRecord)
    [MeasurableSpace (List (FiniteExcursionRecord (Mark K₀)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))))]
    [MeasurableSpace (List (FiniteExcursionRecord (Mark K₁)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))))] :
    Measurable (sourceFineTuple t b w K₀ K₁ ν J h) := by
  exact (measurable_of_countable (exteriorFixedTuple h
    (sourceExteriorFineRecord t b w K₀ K₁ ν))).comp
      (measurable_killedChildRecords _ _ _ _ _)

/-- The actual conditional tuple and the two selected bridge families have exactly the product law
used by the restricted reference-measure comparison. -/
theorem source_conditional_tuple_auxiliary_preserving (t : ℝ) (b w : Site)
    (K₀ K₁ : Finset Site) (ν J : ℕ) (h : ExteriorPathRecord)
    [MeasurableSpace (List (FiniteExcursionRecord (Mark K₀)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))))]
    [MeasurableSpace (List (FiniteExcursionRecord (Mark K₁)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))))]
    (hbw : b ≠ w)
    (hh : 0 < pathLaw.real {ω | sourcePairExteriorRecord t b w ν J ω = h}) :
    MeasurePreserving
      (fun p : Sample × (Site → ℕ → GaussianCoefficientSpace) ↦
        (sourceFineTuple t b w K₀ K₁ ν J h p.1, (p.2 b, p.2 w)))
      (ProbabilityTheory.cond sourceEnlargedLaw
        {p | sourcePairExteriorRecord t b w ν J p.1 = h})
      ((sourceConditionalFineTupleLaw t b w K₀ K₁ ν J h).prod
        ((independentBridgeLaw ℕ).prod (independentBridgeLaw ℕ))) := by
  exact source_conditional_path_map_pair (sourceFineTuple t b w K₀ K₁ ν J h)
    (measurable_sourceFineTuple t b w K₀ K₁ ν J h) t b w ν J hbw h hh

end SRWTightness
