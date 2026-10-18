import SRWTightness.ExteriorRecordComparison
import SRWTightness.SourceExteriorSlotCountLaw

open MeasureTheory Filter
open scoped BigOperators
namespace SRWTightness

/-- The short-root count of one long word, selected by its actual exterior label. -/
noncomputable def sourceExteriorRootCount (t : ℝ) (b w : Site) (ν : ℕ)
    (s : ExteriorSlot) (u : PathWord) : ℕ :=
  let m := sourceLowerRadius t
  let ℓ := sourceRootDepth (Real.exp t) m
  let z := if s.2.1 then w else b
  (wordChildIntervals (sourceEntranceDomain m 1 ℓ z ν)
    (sourceExitDomain m 1 ℓ z ν) s.2.2.1 u).length

/-- The full actual conditional root-count tuple has a geometric product comparison without any
fine-record error. This is the count-only comparison needed before summing the two root totals. -/
theorem source_exterior_count_product (hF : ExteriorBridgeFactorizationInput)
    (hR : TraceExcursionReconstructionInput) (hP : PotentialKernelAsymptoticInput)
    (hH : PositiveHarmonicRelativeInput) (hM : KilledExitDecompositionInput)
    (hT : KilledTraceFactorizationInput) :
    ∃ A C J₀ : ℝ, 0 < A ∧ 0 < C ∧ 3 ≤ J₀ ∧ ∀ᶠ t : ℝ in atTop,
      ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w → 1 ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      J₀ ≤ (J : ℝ) →
      let m := sourceLowerRadius t
      let ℓ := sourceRootDepth (Real.exp t) m
      let K := fun z ↦ sourceEntranceDomain m 1 ℓ z ν
      let D := fun z ↦ sourceExitDomain m 1 ℓ z (ν - J)
      let U := killedChildRecords (diskFinset (Real.exp t)) (K b ∪ K w) (D b ∪ D w)
        0 (fun _ u ↦ u)
      let p := sourceLongEscapeParameter m 1 ℓ ν J
      ∀ h : ExteriorPathRecord, 0 < pathLaw.real {ω | sourcePairExteriorRecord t b w ν J ω = h} →
      ∀ k : Fin h.1.length → ℕ,
      let E := Finset.univ.sum (fun i : Fin h.1.length ↦ A * ((J : ℝ) + 1) * Real.exp (-(J : ℝ)) +
        C * 15 / (sourceRecordRadius m ℓ (ν + 1) - 14) * ((k i : ℝ) + 1))
      let weight := ∏ i : Fin h.1.length, p * (1 - p) ^ k i
      let mass := pathLaw.real {ω |
        (h.1.zip (U ω)).map (fun q ↦ sourceExteriorRootCount t b w ν q.1 q.2) =
          List.ofFn (fun i ↦ k i + 1) ∧ sourcePairExteriorRecord t b w ν J ω = h} /
          pathLaw.real {ω | sourcePairExteriorRecord t b w ν J ω = h}
      Real.exp (-E) * weight ≤ mass ∧ mass ≤ Real.exp E * weight := by
  obtain ⟨A, C, J₀, hA, hC, hJ₀, hslot⟩ :=
    source_exterior_slot_count_law hF hR hP hH hM hT
  refine ⟨A, C, J₀, hA, hC, hJ₀, ?_⟩
  filter_upwards [hslot, source_exterior_geometry] with t ht hg
  intro b w ν J hb hw hbw hd hν hform hJ
  dsimp only
  intro h hh k
  obtain ⟨hkb, hkw, hCD, hgapb, hgapw, _⟩ := hg b w ν J hb hw hbw hd hν hform
  have he := exterior_conditional_word_event hF _ _ _ _ _ 0 hkb hkw hCD hgapb hgapw h hh
    {us | (h.1.zip us).map (fun q ↦ sourceExteriorRootCount t b w ν q.1 q.2) =
      List.ofFn (fun i ↦ k i + 1)}
  simp only [Set.mem_setOf_eq] at he
  simp only [sourcePairExteriorRecord]
  rw [he]
  apply exterior_record_product_comparison
  intro i
  dsimp only
  have hp := ht b w ν J hb hw hbw hd hν hform hJ h hh (h.1.get i) (List.get_mem _ _) (k i)
  cases hl : (h.1.get i).2.1 <;>
    simpa only [killedWordBridgeLaw_record, sourceExteriorRootCount, hl, Bool.false_eq_true,
      if_false, if_true, killedChildIntervals, Set.mem_setOf_eq] using hp

end SRWTightness
