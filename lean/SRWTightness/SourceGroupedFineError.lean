import SRWTightness.SourceActualFineError
import SRWTightness.SourceLongGroupedRecords

open MeasureTheory Filter
namespace SRWTightness

/-- The fine forest at one site, collected inside all actual two-ball long segments in order. -/
noncomputable def sourceGroupedFineForest (t : ℝ) (b w z : Site) (Kobs : Finset Site) (ν J : ℕ)
    (ω : Sample) : List (FiniteExcursionRecord (Mark Kobs)
      (sourceRootDepth (Real.exp t) (sourceLowerRadius t) - (ν + 1))) :=
  let m := sourceLowerRadius t
  let ℓ := sourceRootDepth (Real.exp t) m
  let K := fun y ↦ sourceEntranceDomain m 1 ℓ y ν
  let C := fun y ↦ sourceExitDomain m 1 ℓ y (ν - J)
  (killedChildRecords (diskFinset (Real.exp t)) (K b ∪ K w) (C b ∪ C w) 0
    (fun y u ↦ wordChildRecords (K z) (sourceExitDomain m 1 ℓ z ν) y
      (sourceLongFineRecord t z Kobs ν) u) ω).flatten

/-- The actual grouped forest agrees with the original fine forest and inherits its full success error bound. -/
theorem source_grouped_fine_error (hF : TwoLevelWordFlatteningInput)
    (B W : ℝ) (hB : 0 ≤ B) (hW : 0 ≤ W) :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (ν J : ℕ),
      b ∈ sourceCandidateAnnulus (Real.exp t) → w ∈ sourceCandidateAnnulus (Real.exp t) →
      b ≠ w → 1 ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      ν ≤ 2 * sourceCoarseLowerLevel t →
      ν = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) + J + 5 →
      ∀ z : Site, z = b ∨ z = w → ∀ (Kobs : Finset Site) (a : ℝ),
      1 ≤ a → a ≤ sourceLowerRadius t / t ^ 6 →
      ∀ᵐ ω ∂pathLaw,
        sourceActualFineForest t z Kobs ν ω = sourceGroupedFineForest t b w z Kobs ν J ω ∧
        (sourceActualCount t z 0 ω = 1 → sourceWalkCoarseBand t z ω →
          ((sourceGroupedFineForest t b w z Kobs ν J ω).map
            (sourceLongFineError B W t a Kobs ν)).sum ≤ sourceForestQuadraticError B W 8 t) := by
  filter_upwards [source_actual_fine_error hF B W hB hW, source_actual_nested_words hF,
    source_long_grouped_records hF, source_root_gw_horizon_large, source_continuation_remaining_time,
    eventually_ge_atTop (0 : ℝ)] with t herror hwords hgroup hN htime ht0
  intro b w ν J hb hw hbw ha hν hform z hz Kobs a hamin hcut
  have hzann : z ∈ sourceCandidateAnnulus (Real.exp t) := by rcases hz with rfl | rfl <;> assumption
  have hnreal : (ν : ℝ) ≤ ((sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 : ℕ) : ℝ) := by
    rw [hN.2]
    linarith [htime ν hν]
  have hn : ν ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 := by exact_mod_cast hnreal
  have hi : ν + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) := by
    have hp := hN.1
    omega
  filter_upwards [herror z hzann Kobs ν hi a hamin hcut, hwords z hzann ν hν,
    hgroup b w ν J hb hw hbw ha hν hform z hz (sourceLongFineRecord t z Kobs ν)]
    with ω he hw hg
  rw [hw, killed_child_word_pairs_map] at hg
  have hid : sourceActualFineForest t z Kobs ν ω = sourceGroupedFineForest t b w z Kobs ν J ω := hg
  refine ⟨hid, ?_⟩
  intro hroot hbar
  rw [← hid]
  exact he hroot hbar

end SRWTightness
