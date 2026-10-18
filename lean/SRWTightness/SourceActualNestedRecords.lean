import SRWTightness.SourceNestedWordFlatten
import SRWTightness.SourceCandidateExitDomains
import SRWTightness.SourceEarlyLongEscape
import SRWTightness.SourceWalkSuccessEvent

open MeasureTheory Filter
namespace SRWTightness

/-- Nested finite-word extraction on the killed walk equals direct extraction at its final level. -/
theorem source_forward_nested_records (hF : TwoLevelWordFlatteningInput)
    (m r : ℝ) (ℓ : ℕ) (b : Site) (hr : 0 ≤ r) (hm : sourceRecordBuffer r + 2 ≤ m)
    (k i : ℕ) (hki : k ≤ i) (hi : i + 1 ≤ ℓ) (D : Finset Site) (x : Site)
    (hD : sourceExitDomain m r ℓ b k ⊆ D) :
    actualTerminalWordRecords (sourceExcursionLevels m r ℓ b k (i - k + 1)) D x =ᵐ[pathLaw]
      killedChildRecords D (sourceEntranceDomain m r ℓ b i) (sourceExitDomain m r ℓ b i)
        x (fun y u ↦ (y, u)) := by
  filter_upwards [domainExit_ne_top_ae D x] with ω hfin
  have hh := source_nested_word_flatten hF m r ℓ b hr hm k (i - k) (by omega) x
    (killedPathWord D x ω) (killedPathWord_endpoint_outside_child D _ hD x ω hfin)
  simpa only [show k + (i - k) = i by omega, actualTerminalWordRecords, killedChildRecords] using hh

/-- The actual early source nested root words are the directly scanned root words. -/
theorem source_actual_nested_words (hF : TwoLevelWordFlatteningInput) :
    ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceCandidateAnnulus (Real.exp t), ∀ ν : ℕ,
      ν ≤ 2 * sourceCoarseLowerLevel t →
      let m := sourceLowerRadius t
      let ℓ := sourceRootDepth (Real.exp t) m
      let D := diskFinset (Real.exp t)
      actualTerminalWordRecords (sourceExcursionLevels m 1 ℓ b 0 (ν + 1)) D 0 =ᵐ[pathLaw]
        killedChildRecords D (sourceEntranceDomain m 1 ℓ b ν) (sourceExitDomain m 1 ℓ b ν)
          0 (fun y u ↦ (y, u)) := by
  filter_upwards [source_candidate_exit_domains, source_root_gw_horizon_large,
    source_continuation_remaining_time,
    sourceLowerRadius_tendsto_atTop.eventually (eventually_ge_atTop (16 : ℝ)),
    eventually_ge_atTop (0 : ℝ)] with t hD hN htime hm ht0
  intro b hb ν hν
  dsimp only
  have hnreal : (ν : ℝ) ≤ ((sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 : ℕ) : ℝ) := by
    rw [hN.2]
    linarith [htime ν hν]
  have hn : ν ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) - 1 := by
    exact_mod_cast hnreal
  have hi : ν + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) := by
    have hp := hN.1
    omega
  simpa only [Nat.sub_zero] using source_forward_nested_records hF (sourceLowerRadius t) 1
    (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) b (by norm_num)
    (by norm_num [sourceRecordBuffer]; exact hm) 0 ν (Nat.zero_le _) hi _ 0 (hD b hb 0)

/-- Original manuscript counts agree with direct root scans only after the nested-word identity. -/
theorem source_actual_count_direct (hF : TwoLevelWordFlatteningInput) :
    ∀ᶠ t : ℝ in atTop, ∀ b ∈ sourceCandidateAnnulus (Real.exp t), ∀ ν : ℕ,
      ν ≤ 2 * sourceCoarseLowerLevel t →
      let m := sourceLowerRadius t
      let ℓ := sourceRootDepth (Real.exp t) m
      sourceActualCount t b ν =ᵐ[pathLaw] fun ω ↦
        (killedChildRecords (diskFinset (Real.exp t)) (sourceEntranceDomain m 1 ℓ b ν)
          (sourceExitDomain m 1 ℓ b ν) 0 (fun y u ↦ (y, u)) ω).length := by
  filter_upwards [source_actual_nested_words hF] with t ht
  intro b hb ν hν
  filter_upwards [ht b hb ν hν] with ω hω
  simpa only [sourceActualCount, sourceForwardRecordCount, Nat.sub_zero] using
    congrArg List.length hω

end SRWTightness
