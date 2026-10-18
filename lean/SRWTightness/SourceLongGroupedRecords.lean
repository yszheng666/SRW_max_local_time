import SRWTightness.SourceActualNestedRecords
import SRWTightness.KilledWordFlatten
import SRWTightness.SourceExteriorGeometry

open MeasureTheory Filter
namespace SRWTightness

/-- Original nested short-root records can be regrouped by the actual two-ball long segments.
The equality preserves their order and every selected fine-record map, under the explicit generic
finite-word flattening input. It does not assert independence or replace the original root law. -/
theorem source_long_grouped_records (hF : TwoLevelWordFlatteningInput) :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w → 1 ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      let m := sourceLowerRadius t
      let ℓ := sourceRootDepth (Real.exp t) m
      let D := diskFinset (Real.exp t)
      let K := fun z ↦ sourceEntranceDomain m 1 ℓ z ν
      let C := fun z ↦ sourceExitDomain m 1 ℓ z (ν - J)
      ∀ z : Site, z = b ∨ z = w → ∀ {M : Type} (F : Site → PathWord → M),
      (fun ω ↦ (actualTerminalWordRecords (sourceExcursionLevels m 1 ℓ z 0 (ν + 1)) D 0 ω).map
        (fun p ↦ F p.1 p.2)) =ᵐ[pathLaw]
        fun ω ↦ (killedChildRecords D (K b ∪ K w) (C b ∪ C w) 0
          (fun y u ↦ wordChildRecords (K z) (sourceExitDomain m 1 ℓ z ν) y F u) ω).flatten := by
  filter_upwards [source_actual_nested_words hF, source_exterior_geometry,
    source_root_gw_horizon_large, source_continuation_remaining_time,
    sourceLowerRadius_tendsto_atTop.eventually (eventually_ge_atTop (16 : ℝ)),
    eventually_ge_atTop (0 : ℝ)] with t hwords hgeom hN htime hm16 ht0
  intro b w ν J hb hw hbw ha hν hform
  dsimp only
  intro z hz M F
  let m := sourceLowerRadius t
  let ℓ := sourceRootDepth (Real.exp t) m
  let K := fun z ↦ sourceEntranceDomain m 1 ℓ z ν
  let C := fun z ↦ sourceExitDomain m 1 ℓ z (ν - J)
  obtain ⟨hKb, hKw, hCD, _, _, _⟩ := hgeom b w ν J hb hw hbw ha hν hform
  have hKC : K b ∪ K w ⊆ C b ∪ C w := Finset.union_subset_union hKb hKw
  have hzann : z ∈ sourceCandidateAnnulus (Real.exp t) := by rcases hz with rfl | rfl <;> assumption
  have hnreal : (ν : ℝ) ≤ ((ℓ - 1 : ℕ) : ℝ) := by
    change (ν : ℝ) ≤ ((sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 : ℕ) : ℝ)
    rw [hN.2]
    linarith [htime ν hν]
  have hn : ν ≤ ℓ - 1 := by exact_mod_cast hnreal
  have hi : ν + 1 ≤ ℓ := by have hp : 0 < ℓ - 1 := hN.1; omega
  have hm : sourceRecordBuffer 1 + 2 ≤ m := by norm_num [sourceRecordBuffer]; exact hm16
  have hshort : K z ⊆ sourceExitDomain m 1 ℓ z ν :=
    sourceEntranceDomain_subset_exit m 1 ℓ z ν (by norm_num) hm hi
  have hK : K z ⊆ K b ∪ K w := by
    rcases hz with rfl | rfl
    · exact Finset.subset_union_left
    · exact Finset.subset_union_right
  have hC : sourceExitDomain m 1 ℓ z ν ⊆ C b ∪ C w := by
    have hh : sourceExitDomain m 1 ℓ z ν ⊆ C z :=
      sourceExitDomain_antitone m 1 ℓ z (by norm_num) hm (Nat.sub_le ν J)
    rcases hz with rfl | rfl
    · exact hh.trans Finset.subset_union_left
    · exact hh.trans Finset.subset_union_right
  have hg := killed_child_records_flatten hF (diskFinset (Real.exp t))
    (K b ∪ K w) (C b ∪ C w) (K z) (sourceExitDomain m 1 ℓ z ν)
    hKC hshort hK hC hCD 0 F
  filter_upwards [hwords z hzann ν hν, hg] with ω hω hgω
  rw [hω, killed_child_word_pairs_map]
  exact hgω.symm

/-- Grouped short-root totals retain the actual source count on the common original path. -/
theorem source_long_grouped_root_count (hF : TwoLevelWordFlatteningInput) :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w → 1 ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      let m := sourceLowerRadius t
      let ℓ := sourceRootDepth (Real.exp t) m
      let K := fun z ↦ sourceEntranceDomain m 1 ℓ z ν
      let C := fun z ↦ sourceExitDomain m 1 ℓ z (ν - J)
      ∀ z : Site, z = b ∨ z = w → sourceActualCount t z ν =ᵐ[pathLaw]
        fun ω ↦ ((killedChildRecords (diskFinset (Real.exp t)) (K b ∪ K w) (C b ∪ C w) 0
          (fun y u ↦ wordChildRecords (K z) (sourceExitDomain m 1 ℓ z ν) y
            (fun x v ↦ (x, v)) u) ω).flatten).length := by
  filter_upwards [source_long_grouped_records hF] with t ht
  intro b w ν J hb hw hbw ha hν hform
  dsimp only
  intro z hz
  filter_upwards [ht b w ν J hb hw hbw ha hν hform z hz (fun x v ↦ (x, v))] with ω hω
  simpa only [List.length_map, sourceActualCount, sourceForwardRecordCount, Nat.sub_zero] using
    congrArg List.length hω

end SRWTightness
