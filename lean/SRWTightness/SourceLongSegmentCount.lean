import SRWTightness.WordLongSegmentCount
import SRWTightness.SourceLongGroupedRecords
import SRWTightness.SourceOriginalJointRootBound

open MeasureTheory Filter
namespace SRWTightness

/-- The number of long segments is the number of headers in the actual exterior record. -/
noncomputable def sourceLongSegmentCount (t : ℝ) (b w : Site) (ν J : ℕ) (ω : Sample) : ℕ :=
  (sourcePairExteriorRecord t b w ν J ω).1.length

/-- The actual number of long segments is at most the two original short-root counts combined. -/
theorem source_long_segment_count_bound (hF : TwoLevelWordFlatteningInput) :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w → 1 ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      ∀ᵐ ω ∂pathLaw, sourceLongSegmentCount t b w ν J ω ≤
        sourceActualCount t b ν ω + sourceActualCount t w ν ω := by
  filter_upwards [source_long_grouped_root_count hF, source_root_gw_horizon_large,
    source_continuation_remaining_time,
    sourceLowerRadius_tendsto_atTop.eventually (eventually_ge_atTop (16 : ℝ)),
    eventually_ge_atTop (0 : ℝ)] with t hgroup hN htime hm16 ht0
  intro b w ν J hb hw hbw ha hν hform
  let m := sourceLowerRadius t
  let ℓ := sourceRootDepth (Real.exp t) m
  let K := fun z ↦ sourceEntranceDomain m 1 ℓ z ν
  let Cshort := fun z ↦ sourceExitDomain m 1 ℓ z ν
  let C := fun z ↦ sourceExitDomain m 1 ℓ z (ν - J)
  have hnreal : (ν : ℝ) ≤ ((ℓ - 1 : ℕ) : ℝ) := by
    change (ν : ℝ) ≤ ((sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 : ℕ) : ℝ)
    rw [hN.2]
    linarith [htime ν hν]
  have hn : ν ≤ ℓ - 1 := by exact_mod_cast hnreal
  have hi : ν + 1 ≤ ℓ := by have hp : 0 < ℓ - 1 := hN.1; omega
  have hm : sourceRecordBuffer 1 + 2 ≤ m := by norm_num [sourceRecordBuffer]; exact hm16
  have hK (z : Site) : K z ⊆ Cshort z :=
    sourceEntranceDomain_subset_exit m 1 ℓ z ν (by norm_num) hm hi
  have hC (z : Site) : Cshort z ⊆ C z :=
    sourceExitDomain_antitone m 1 ℓ z (by norm_num) hm (Nat.sub_le ν J)
  filter_upwards [hgroup b w ν J hb hw hbw ha hν hform b (Or.inl rfl),
    hgroup b w ν J hb hw hbw ha hν hform w (Or.inr rfl)] with ω hbω hwω
  rw [hbω, hwω]
  have hh := word_long_segment_count (K b) (Cshort b) (K w) (Cshort w) (C b ∪ C w)
    (hK b) (hK w) ((hC b).trans Finset.subset_union_left)
    ((hC w).trans Finset.subset_union_right) 0 (killedPathWord (diskFinset (Real.exp t)) 0 ω)
  simpa only [sourceLongSegmentCount, sourcePairExteriorRecord, killedExteriorRecord,
    wordExteriorRecord, packExteriorRecord_length, killedChildRecords] using hh

end SRWTightness
