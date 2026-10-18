import SRWTightness.SourceFineReferenceMeasure
import SRWTightness.OrderedTaggedForestMixture

namespace SRWTightness

/-- The generic ordered block weight is exactly the weight already used in the source comparison. -/
theorem source_fine_block_weight (t : ℝ) (b : Site) (K : Finset Site) (ν J : ℕ)
    [MeasurableSpace (FiniteExcursionRecord (Mark K)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1)))]
    [MeasurableSingletonClass (FiniteExcursionRecord (Mark K)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1)))]
    (rs : List (FiniteExcursionRecord (Mark K)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1)))) :
    orderedForestBlockWeight (sourceLongEscapeParameter (sourceLowerRadius t) 1
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) ν J)
      (sourceFineReferenceMeasure t b K ν) rs = sourceLongFineListWeight t b K ν J rs := by
  cases rs with
  | nil => simp [orderedForestBlockWeight, sourceLongFineListWeight]
  | cons r rs => simp only [orderedForestBlockWeight, List.cons_ne_nil, if_false,
      List.length_cons, Nat.add_sub_cancel, sourceLongFineListWeight,
      sourceFineReferenceMeasure_singleton]

/-- The selected tagged generic block weight is precisely the source tagged weight. -/
theorem source_tagged_block_weight (t : ℝ) (b w : Site) (K₀ K₁ : Finset Site) (ν J : ℕ)
    [MeasurableSpace (FiniteExcursionRecord (Mark K₀)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1)))]
    [MeasurableSingletonClass (FiniteExcursionRecord (Mark K₀)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1)))]
    [MeasurableSpace (FiniteExcursionRecord (Mark K₁)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1)))]
    [MeasurableSingletonClass (FiniteExcursionRecord (Mark K₁)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1)))]
    (r : SourceExteriorFineValue t K₀ K₁ ν) :
    r.elim
      (orderedForestBlockWeight (sourceLongEscapeParameter (sourceLowerRadius t) 1
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) ν J)
        (sourceFineReferenceMeasure t b K₀ ν))
      (orderedForestBlockWeight (sourceLongEscapeParameter (sourceLowerRadius t) 1
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) ν J)
        (sourceFineReferenceMeasure t w K₁ ν)) =
      sourceExteriorFineWeight t b w K₀ K₁ ν J r := by
  cases r with
  | inl rs => exact source_fine_block_weight t b K₀ ν J rs
  | inr rs => exact source_fine_block_weight t w K₁ ν J rs

end SRWTightness
