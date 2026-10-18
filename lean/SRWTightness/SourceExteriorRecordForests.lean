import SRWTightness.SourceExteriorRecordValues
import SRWTightness.SourceExteriorLabelSupport
import SRWTightness.SourceExteriorFineForest

open Filter
namespace SRWTightness

/-- Concatenate the left-labeled forests, preserving their original order. -/
def taggedForestLeft {α β : Type*} (rs : List (Sum (List α) (List β))) : List α :=
  rs.flatMap (fun r ↦ r.elim id (fun _ ↦ []))

/-- Concatenate the right-labeled forests, preserving their original order. -/
def taggedForestRight {α β : Type*} (rs : List (Sum (List α) (List β))) : List β :=
  rs.flatMap (fun r ↦ r.elim (fun _ ↦ []) id)

/-- Positive actual word fibers yield compatible tagged records and reconstruct both original
grouped fine forests. The support threshold is uniform in the observation sets and record depth. -/
theorem source_exterior_tagged_forests (hF : ExteriorBridgeFactorizationInput) :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w → 1 ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      let m := sourceLowerRadius t
      let ℓ := sourceRootDepth (Real.exp t) m
      let K := fun z ↦ sourceEntranceDomain m 1 ℓ z ν
      let D := fun z ↦ sourceExitDomain m 1 ℓ z (ν - J)
      let U := killedChildRecords (diskFinset (Real.exp t)) (K b ∪ K w) (D b ∪ D w)
        0 (fun _ u ↦ u)
      ∀ (K₀ K₁ : Finset Site) (h : ExteriorPathRecord) (us : List PathWord),
      us.length = h.1.length →
      0 < pathLaw.real {ω | sourcePairExteriorRecord t b w ν J ω = h} →
      0 < pathLaw.real {ω | U ω = us ∧ sourcePairExteriorRecord t b w ν J ω = h} →
      let vs := (h.1.zip us).map (fun p ↦ sourceExteriorFineRecord t b w K₀ K₁ ν p.1 p.2)
      (∀ p ∈ h.1.zip us, sourceExteriorFineCompatible t K₀ K₁ ν p.1
        (sourceExteriorFineRecord t b w K₀ K₁ ν p.1 p.2)) ∧
      ∀ ω : Sample, sourcePairExteriorRecord t b w ν J ω = h → U ω = us →
        taggedForestLeft vs = sourceGroupedFineForest t b w b K₀ ν J ω ∧
        taggedForestRight vs = sourceGroupedFineForest t b w w K₁ ν J ω := by
  filter_upwards [source_exterior_label_support (M₀ := Unit) (M₁ := Unit) hF] with t ht
  intro b w ν J hb hw hbw hd hν hform
  dsimp only
  intro K₀ K₁ h us hlen hh hu
  have hs := ht b w ν J hb hw hbw hd hν hform h us hlen hh hu
    (fun _ _ ↦ ()) (fun _ _ ↦ ())
  constructor
  · intro p hp
    have hsp := hs p hp
    cases hl : p.1.2.1
    · have hn := (hsp.1 hl).1
      have hn' : wordChildRecords
          (sourceEntranceDomain (sourceLowerRadius t) 1
            (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) b ν)
          (sourceExitDomain (sourceLowerRadius t) 1
            (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) b ν)
          p.1.2.2.1 (sourceLongFineRecord t b K₀ ν) p.2 ≠ [] := by
        simpa only [wordChildRecords, ne_eq, List.map_eq_nil_iff] using hn
      simpa only [sourceExteriorFineRecord, sourceExteriorFineCompatible, hl,
        Bool.false_eq_true, if_false, Sum.elim_inl, true_and] using hn'
    · have hn := (hsp.2 hl).1
      have hn' : wordChildRecords
          (sourceEntranceDomain (sourceLowerRadius t) 1
            (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) w ν)
          (sourceExitDomain (sourceLowerRadius t) 1
            (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) w ν)
          p.1.2.2.1 (sourceLongFineRecord t w K₁ ν) p.2 ≠ [] := by
        simpa only [wordChildRecords, ne_eq, List.map_eq_nil_iff] using hn
      simpa only [sourceExteriorFineRecord, sourceExteriorFineCompatible, hl,
        if_true, Sum.elim_inr, true_and] using hn'
  · intro ω hω huω
    constructor
    · refine Eq.trans ?_ (source_exterior_fine_forest t b w b K₀ ν J ω h us hω huω)
      simp only [taggedForestLeft, List.flatMap_map]
      apply List.flatMap_congr
      intro p hp
      have hsp := hs p hp
      cases hl : p.1.2.1
      · simp only [sourceExteriorFineRecord, hl, Bool.false_eq_true, if_false, Sum.elim_inl, id_eq]
      · have hz : wordChildRecords
            (sourceEntranceDomain (sourceLowerRadius t) 1
              (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) b ν)
            (sourceExitDomain (sourceLowerRadius t) 1
              (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) b ν)
            p.1.2.2.1 (sourceLongFineRecord t b K₀ ν) p.2 = [] := by
          simpa only [wordChildRecords, ne_eq, List.map_eq_nil_iff] using (hsp.2 hl).2
        simpa only [sourceExteriorFineRecord, hl, if_true, Sum.elim_inr] using hz.symm
    · refine Eq.trans ?_ (source_exterior_fine_forest t b w w K₁ ν J ω h us hω huω)
      simp only [taggedForestRight, List.flatMap_map]
      apply List.flatMap_congr
      intro p hp
      have hsp := hs p hp
      cases hl : p.1.2.1
      · have hz : wordChildRecords
            (sourceEntranceDomain (sourceLowerRadius t) 1
              (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) w ν)
            (sourceExitDomain (sourceLowerRadius t) 1
              (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) w ν)
            p.1.2.2.1 (sourceLongFineRecord t w K₁ ν) p.2 = [] := by
          simpa only [wordChildRecords, ne_eq, List.map_eq_nil_iff] using (hsp.1 hl).2
        simpa only [sourceExteriorFineRecord, hl, Bool.false_eq_true, if_false, Sum.elim_inl] using hz.symm
      · simp only [sourceExteriorFineRecord, hl, if_true, Sum.elim_inr, id_eq]

end SRWTightness
