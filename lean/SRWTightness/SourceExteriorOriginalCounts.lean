import SRWTightness.ExteriorCountTotals
import SRWTightness.SourceExteriorCountProduct
import SRWTightness.SourceExteriorLabelSupport
import SRWTightness.SourceLongGroupedRecords
import SRWTightness.ExteriorWordAlignment
import SRWTightness.PositiveAtomSupport

open MeasureTheory Filter
namespace SRWTightness

/-- On every positive exterior atom, the labeled totals of the actual short-root tuple are the
original two root counts, almost surely. Their original dependence is retained. -/
theorem source_exterior_original_counts (hExt : ExteriorBridgeFactorizationInput)
    (hFlat : TwoLevelWordFlatteningInput) :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w → 1 ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      let m := sourceLowerRadius t
      let ℓ := sourceRootDepth (Real.exp t) m
      let K := fun z ↦ sourceEntranceDomain m 1 ℓ z ν
      let C := fun z ↦ sourceExitDomain m 1 ℓ z (ν - J)
      let U := killedChildRecords (diskFinset (Real.exp t)) (K b ∪ K w) (C b ∪ C w)
        0 (fun _ u ↦ u)
      ∀ h : ExteriorPathRecord, 0 < pathLaw.real {ω | sourcePairExteriorRecord t b w ν J ω = h} →
      ∀ᵐ ω ∂pathLaw, sourcePairExteriorRecord t b w ν J ω = h →
      ∀ r : Fin h.1.length → ℕ,
      (h.1.zip (U ω)).map (fun p ↦ sourceExteriorRootCount t b w ν p.1 p.2) = List.ofFn r →
      sourceActualCount t b ν ω = labeledRootTotal (fun i ↦ (h.1.get i).2.1) r false ∧
      sourceActualCount t w ν ω = labeledRootTotal (fun i ↦ (h.1.get i).2.1) r true := by
  filter_upwards [source_exterior_label_support (M₀ := Unit) (M₁ := Unit) hExt,
    source_long_grouped_root_count hFlat] with t hsupp hgroup
  intro b w ν J hb hw hbw hd hν hform
  dsimp only
  let m := sourceLowerRadius t
  let ℓ := sourceRootDepth (Real.exp t) m
  let K := fun z ↦ sourceEntranceDomain m 1 ℓ z ν
  let S := fun z ↦ sourceExitDomain m 1 ℓ z ν
  let C := fun z ↦ sourceExitDomain m 1 ℓ z (ν - J)
  let U := killedChildRecords (diskFinset (Real.exp t)) (K b ∪ K w) (C b ∪ C w) 0 (fun _ u ↦ u)
  let Z := sourcePairExteriorRecord t b w ν J
  have hpos := ae_support_of_positive_atoms pathLaw (fun ω ↦ (U ω, Z ω))
    (fun r ↦ 0 < pathLaw.real {ω | (U ω, Z ω) = r}) (fun _ hr ↦ hr)
  intro h hh
  filter_upwards [hpos, hgroup b w ν J hb hw hbw hd hν hform b (Or.inl rfl),
    hgroup b w ν J hb hw hbw hd hν hform w (Or.inr rfl)] with ω hp hx hy
  intro hω r hr
  change Z ω = h at hω
  have hlen : (U ω).length = h.1.length := by
    have he := killedExteriorRecord_length (diskFinset (Real.exp t)) (K b ∪ K w)
      (C b ∪ C w) (twoDomainExteriorLabel (K w)) 0 ω
    change (Z ω).1.length = (U ω).length at he
    rw [hω] at he
    exact he.symm
  have hp' : 0 < pathLaw.real {ω' | U ω' = U ω ∧ Z ω' = h} := by
    simpa only [Prod.mk.injEq, hω] using hp
  have hs := hsupp b w ν J hb hw hbw hd hν hform h (U ω) hlen hh hp'
    (fun _ _ ↦ ()) (fun _ _ ↦ ())
  have he₀ := exterior_word_fiber_records (diskFinset (Real.exp t)) (K b ∪ K w) (C b ∪ C w)
    (twoDomainExteriorLabel (K w)) 0 ω h (U ω) hω rfl
    (fun y u ↦ wordChildRecords (K b) (S b) y (fun x v ↦ (x, v)) u)
  have he₁ := exterior_word_fiber_records (diskFinset (Real.exp t)) (K b ∪ K w) (C b ∪ C w)
    (twoDomainExteriorLabel (K w)) 0 ω h (U ω) hω rfl
    (fun y u ↦ wordChildRecords (K w) (S w) y (fun x v ↦ (x, v)) u)
  have hx' := hx.trans (congrArg (fun rs ↦ rs.flatten.length) he₀).symm
  have hy' := hy.trans (congrArg (fun rs ↦ rs.flatten.length) he₁).symm
  simp only [List.length_flatten, List.map_map, Function.comp_def, wordChildRecords, List.length_map] at hx' hy'
  constructor
  · rw [hx', exterior_count_total_of_tuple h (U ω) (sourceExteriorRootCount t b w ν) r hr false]
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    cases hl : p.1.2.1
    · simp [sourceExteriorRootCount, hl, K, S, m, ℓ]
    · have hz : wordChildIntervals (K b) (S b) p.1.2.2.1 p.2 = [] := by
        simpa only [wordChildRecords, List.map_eq_nil_iff] using ((hs p hp).2 hl).2
      simp [sourceExteriorRootCount, hl, hz]
  · rw [hy', exterior_count_total_of_tuple h (U ω) (sourceExteriorRootCount t b w ν) r hr true]
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    cases hl : p.1.2.1
    · have hz : wordChildIntervals (K w) (S w) p.1.2.2.1 p.2 = [] := by
        simpa only [wordChildRecords, List.map_eq_nil_iff] using ((hs p hp).1 hl).2
      simp [sourceExteriorRootCount, hl, hz]
    · simp [sourceExteriorRootCount, hl, K, S, m, ℓ]

end SRWTightness
