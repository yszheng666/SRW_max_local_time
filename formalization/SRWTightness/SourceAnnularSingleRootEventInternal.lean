import SRWTightness.SourceAnnularSingleRoot
import SRWTightness.SingleRootEventComparison
import SRWTightness.SourceProfileReferenceProbabilityInternal

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

/-- Actual one-root source events have both bounds without an assumed marked-tree law. -/
theorem source_annular_single_root_event_internal (hinput : PotentialKernelAsymptoticInput) :
    ∃ B W c T : ℝ, 0 ≤ B ∧ 0 ≤ W ∧ 0 < c ∧
    ∀ (b : Site) (t a : ℝ) (K : Finset Site),
      T ≤ t → 1 ≤ a → a ≤ sourceLowerRadius t / t ^ 6 →
      K ⊆ translateFinset b (diskFinset a) →
      Real.exp t / 4 ≤ Real.sqrt (normSq b) → Real.sqrt (normSq b) ≤ Real.exp t / 3 →
      ∀ ℓ : ℕ, ℓ = sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      ∀ [MeasurableSpace (FiniteExcursionRecord (Mark K) (ℓ - 1))]
        [MeasurableSingletonClass (FiniteExcursionRecord (Mark K) (ℓ - 1))]
        [MeasurableSpace (List (FiniteExcursionRecord (Mark K) (ℓ - 1)))]
        [MeasurableSingletonClass (List (FiniteExcursionRecord (Mark K) (ℓ - 1)))],
      let n := ℓ - 1
      let η := finiteRecordError
        (fun i ↦ 4 * (B * 14 / growingRecordRadius (sourceLowerRadius t) i))
        (fun _ : Mark K ↦ 2 * (W * (a + 1) / sourceLowerRadius t *
          Real.log (sourceLowerRadius t / a))) n
      let μ := finiteRecordReferenceMeasure
        (referenceMarkLaw
          (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))) K
          (sourceReferenceIntensity (sourceLowerRadius t) 14)) n
      ∀ (s : Set (List (FiniteExcursionRecord (Mark K) n))) (E : ℝ),
        (∀ rs ∈ s, rs.length = 1) → (∀ r, [r] ∈ s → η r ≤ E) →
      let p := pathLaw {ω | killedChildRecords (diskFinset (Real.exp t))
          (sourceEntranceDomain (sourceLowerRadius t) 1 ℓ b 0)
          (sourceExitDomain (sourceLowerRadius t) 1 ℓ b 0) 0
          (actualFiniteWordRecord (sourceTreeEntrance (sourceLowerRadius t) 1 ℓ b)
            (sourceTreeExit (sourceLowerRadius t) 1 ℓ b) (wordOccupationMark K) n) ω ∈ s}
      ENNReal.ofReal (c * Real.exp (-E)) * independentForestLaw μ 1 s ≤ p ∧
        p ≤ ENNReal.ofReal (Real.exp E) * independentForestLaw μ 1 s := by
  obtain ⟨B, W, c, T, hB, hW, hc, hh⟩ := source_annular_single_root hinput
  refine ⟨B, W, c, max T sourceCapacityHalfThreshold, hB, hW, hc, ?_⟩
  intro b t a K ht ha hcut hK hblo hbhi ℓ hℓ
  intro inst₁ inst₂ inst₃ inst₄
  dsimp only
  intro s E hlen herr
  have htT : T ≤ t := (le_max_left _ _).trans ht
  have htcap : sourceCapacityHalfThreshold ≤ t := (le_max_right _ _).trans ht
  letI := finiteExcursionRecord_countable (Mark K) (ℓ - 1)
  letI := source_profile_reference_probability_internal b t a K htcap ha hcut hK (ℓ - 1)
  apply single_root_event_comparison pathLaw _ _ _ c E hc.le s hlen ?_ herr ?_
  · intro rs hrs
    exact measurableSet_killedChildRecords_eq _ _ _ _ _ rs
  · intro r hrs
    rw [finiteRecordReferenceMeasure_real_singleton]
    have hr := hh b t a K htT ha hcut hK hblo hbhi ℓ hℓ r
    have hset : {ω | (killedChildIntervals (diskFinset (Real.exp t))
        (sourceEntranceDomain (sourceLowerRadius t) 1 ℓ b 0)
        (sourceExitDomain (sourceLowerRadius t) 1 ℓ b 0) 0 ω).length = 1 ∧
        killedChildRecords (diskFinset (Real.exp t))
          (sourceEntranceDomain (sourceLowerRadius t) 1 ℓ b 0)
          (sourceExitDomain (sourceLowerRadius t) 1 ℓ b 0) 0
          (actualFiniteWordRecord (sourceTreeEntrance (sourceLowerRadius t) 1 ℓ b)
            (sourceTreeExit (sourceLowerRadius t) 1 ℓ b) (wordOccupationMark K) (ℓ - 1)) ω = [r]} =
        {ω | killedChildRecords (diskFinset (Real.exp t))
          (sourceEntranceDomain (sourceLowerRadius t) 1 ℓ b 0)
          (sourceExitDomain (sourceLowerRadius t) 1 ℓ b 0) 0
          (actualFiniteWordRecord (sourceTreeEntrance (sourceLowerRadius t) 1 ℓ b)
            (sourceTreeExit (sourceLowerRadius t) 1 ℓ b) (wordOccupationMark K) (ℓ - 1)) ω =
              [r]} := by
      ext ω
      constructor
      · exact fun h ↦ h.2
      · intro h
        refine ⟨?_, h⟩
        rw [← killedChildRecords_length _ _ _ _
          (actualFiniteWordRecord (sourceTreeEntrance (sourceLowerRadius t) 1 ℓ b)
            (sourceTreeExit (sourceLowerRadius t) 1 ℓ b) (wordOccupationMark K) (ℓ - 1)) ω,
          h, List.length_singleton]
    dsimp only at hr
    rw [hset] at hr
    exact hr

end SRWTightness
