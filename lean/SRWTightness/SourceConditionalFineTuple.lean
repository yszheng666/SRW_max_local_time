import SRWTightness.ExteriorFixedTuple
import SRWTightness.SourceExteriorRecordProduct
import SRWTightness.OrderedTaggedForestMixture

open MeasureTheory
namespace SRWTightness

/-- The actual finite fine-record tuple law conditional on the original exterior record. -/
noncomputable def sourceConditionalFineTupleLaw (t : ℝ) (b w : Site)
    (K₀ K₁ : Finset Site) (ν J : ℕ) (h : ExteriorPathRecord)
    [MeasurableSpace (List (FiniteExcursionRecord (Mark K₀)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))))]
    [MeasurableSpace (List (FiniteExcursionRecord (Mark K₁)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))))] :
    Measure (Fin h.1.length → SourceExteriorFineValue t K₀ K₁ ν) :=
  let m := sourceLowerRadius t
  let ℓ := sourceRootDepth (Real.exp t) m
  let K := fun z ↦ sourceEntranceDomain m 1 ℓ z ν
  let D := fun z ↦ sourceExitDomain m 1 ℓ z (ν - J)
  (ProbabilityTheory.cond pathLaw {ω | sourcePairExteriorRecord t b w ν J ω = h}).map
    (fun ω ↦ exteriorFixedTuple h (sourceExteriorFineRecord t b w K₀ K₁ ν)
      (killedChildRecords (diskFinset (Real.exp t)) (K b ∪ K w) (D b ∪ D w)
        0 (fun _ u ↦ u) ω))

/-- Positive exterior atoms make the actual conditional tuple law a probability measure. -/
theorem sourceConditionalFineTupleLaw_probability (t : ℝ) (b w : Site)
    (K₀ K₁ : Finset Site) (ν J : ℕ) (h : ExteriorPathRecord)
    [MeasurableSpace (List (FiniteExcursionRecord (Mark K₀)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))))]
    [MeasurableSpace (List (FiniteExcursionRecord (Mark K₁)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))))]
    (hh : 0 < pathLaw.real {ω | sourcePairExteriorRecord t b w ν J ω = h}) :
    IsProbabilityMeasure (sourceConditionalFineTupleLaw t b w K₀ K₁ ν J h) := by
  have hμ : pathLaw {ω | sourcePairExteriorRecord t b w ν J ω = h} ≠ 0 := by
    intro hz
    exact hh.ne' ((measureReal_eq_zero_iff (measure_ne_top _ _)).mpr hz)
  letI := ProbabilityTheory.cond_isProbabilityMeasure hμ
  unfold sourceConditionalFineTupleLaw
  apply Measure.isProbabilityMeasure_map
  exact ((measurable_of_countable (exteriorFixedTuple h
    (sourceExteriorFineRecord t b w K₀ K₁ ν))).comp
      (measurable_killedChildRecords _ _ _ _ _)).aemeasurable

/-- Actual tuple atoms are exactly the conditional chronological record atoms already compared. -/
theorem sourceConditionalFineTupleLaw_atom (t : ℝ) (b w : Site)
    (K₀ K₁ : Finset Site) (ν J : ℕ) (h : ExteriorPathRecord)
    [MeasurableSpace (List (FiniteExcursionRecord (Mark K₀)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))))]
    [MeasurableSingletonClass (List (FiniteExcursionRecord (Mark K₀)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))))]
    [MeasurableSpace (List (FiniteExcursionRecord (Mark K₁)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))))]
    [MeasurableSingletonClass (List (FiniteExcursionRecord (Mark K₁)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))))]
    (r : Fin h.1.length → SourceExteriorFineValue t K₀ K₁ ν) :
    let m := sourceLowerRadius t
    let ℓ := sourceRootDepth (Real.exp t) m
    let K := fun z ↦ sourceEntranceDomain m 1 ℓ z ν
    let D := fun z ↦ sourceExitDomain m 1 ℓ z (ν - J)
    (sourceConditionalFineTupleLaw t b w K₀ K₁ ν J h).real {r} =
      pathLaw.real {ω | (h.1.zip (killedChildRecords (diskFinset (Real.exp t))
        (K b ∪ K w) (D b ∪ D w) 0 (fun _ u ↦ u) ω)).map
        (fun p ↦ sourceExteriorFineRecord t b w K₀ K₁ ν p.1 p.2) = List.ofFn r ∧
          sourcePairExteriorRecord t b w ν J ω = h} /
        pathLaw.real {ω | sourcePairExteriorRecord t b w ν J ω = h} := by
  exact exterior_conditional_tuple_atom _ _ _ _ _ h _ r

end SRWTightness
