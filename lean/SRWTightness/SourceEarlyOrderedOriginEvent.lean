import SRWTightness.SourceEarlyOrderedRecordComparison
import SRWTightness.SourceEarlyCommonPrefixError
import SRWTightness.DiskForestReferenceUpper
import SRWTightness.FiniteRecordReferenceMeasure
import SRWTightness.SingleRootReferenceEvent

open MeasureTheory Filter
open scoped ENNReal
namespace SRWTightness

/-- Origin-started single-root common-prefix events obey the reference upper comparison. -/
theorem source_early_ordered_origin_event_upper (hinput : PotentialKernelAsymptoticInput) :
    ∃ E : ℝ, 0 ≤ E ∧ ∃ Jmin : ℕ, ∀ J₀ : ℕ, Jmin ≤ J₀ →
      ∃ a₀ : ℕ, 1 ≤ a₀ ∧ ∀ᶠ t : ℝ in atTop, ∀ b w : Site, b ≠ w →
      a₀ ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) <
        sourceCoarseLowerLevel t + sourceCommonPairGap t →
      let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
      let j := a - sourceEarlyDistanceGap a J₀
      let m := sourceCommonPairInnerRadius t j
      let K := sourceCommonPairObservation b w
      let μ := referenceWordMarkLaw (translateFinset b (diskFinset (Real.exp 1 * m + 14))) K
        (sourceReferenceIntensity m 14)
      Real.sqrt (normSq b) + (Real.exp 1 * growingRecordRadius m j + 14) + 1 < Real.exp t →
      growingRecordRadius m j - 14 ≤ Real.sqrt (normSq b) →
      ∀ [MeasurableSpace (FiniteExcursionRecord WordMark j)]
        [MeasurableSingletonClass (FiniteExcursionRecord WordMark j)]
        [MeasurableSpace (List (FiniteExcursionRecord WordMark j))]
        [MeasurableSingletonClass (List (FiniteExcursionRecord WordMark j))],
      MarkedGWTreeInput WordMark →
      ∀ s : Set (FiniteExcursionRecord WordMark j),
      (∀ r ∈ s, ∀ k : ℕ, 0 < k → k ≤ j →
        geometricGWHeight (finiteRecordPopulationList j r) k ≤
          4 + sourceBarrierSlope t * k -
            (min (k : ℝ) (sourceTotalTime t - k)) ^ (2 / 5 : ℝ)) →
      pathLaw {ω | ∃ r ∈ s, killedChildRecords (diskFinset (Real.exp t))
        (growingRecordEntrance b m 14 j) (growingRecordExit b m 14 j) 0
        (actualFiniteWordRecord (growingRecordEntrance b m 14)
          (growingRecordExit b m 14)
          (firstEntranceWordOfWord (growingRecordExit b m 14 0) K) j) ω = [r]} ≤
        ENNReal.ofReal (Real.exp E) * finiteRecordReferenceMass μ j s := by
  obtain ⟨B, W, hB, hW, JR, hc⟩ := source_early_ordered_record_comparison hinput
  obtain ⟨JE, he⟩ := source_early_common_prefix_error B W hB hW
  obtain ⟨JG, hg⟩ := source_early_ordered_conditions B W 0 0 hB hW
  let E := 57 * (128 * B + 48 * Real.exp 1 * W)
  refine ⟨E, by dsimp [E]; positivity, max JR (max JE JG), ?_⟩
  intro J₀ hJ₀
  obtain ⟨aR, haR, hc⟩ := hc J₀ ((le_max_left _ _).trans hJ₀)
  obtain ⟨aE, haE, he⟩ := he J₀
    (((le_max_left _ _).trans (le_max_right _ _)).trans hJ₀)
  obtain ⟨aG, haG, hg⟩ := hg J₀
    (((le_max_right _ _).trans (le_max_right _ _)).trans hJ₀)
  refine ⟨aR + aE + aG, by omega, ?_⟩
  filter_upwards [hc, he, hg] with t hc he hg
  intro b w hbw ha hrange
  dsimp only
  intro hfit hout inst₁ inst₂ inst₃ inst₄ hmarked s hbar
  let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
  let j := a - sourceEarlyDistanceGap a J₀
  let m := sourceCommonPairInnerRadius t j
  let K := sourceCommonPairObservation b w
  let μ := referenceWordMarkLaw (translateFinset b (diskFinset (Real.exp 1 * m + 14))) K
    (sourceReferenceIntensity m 14)
  let η := finiteRecordError (fun i ↦ 4 * (B * 14 / growingRecordRadius m i))
    (fun _ : WordMark ↦ 2 * (W * (2 * Real.sqrt (normSq (w - b)) + 1) / m *
      Real.log (m / (2 * Real.sqrt (normSq (w - b)))))) j
  obtain ⟨hm, _, _, _, _, _, hcap, _⟩ := hg b w hbw (show aG ≤ _ by omega) hrange
  change 112 ≤ m at hm
  have hm0 : 0 < m := sourceCommonPairInnerRadius_pos t j
  have hrad := growingRecordRadius_ge_base m hm0.le j
  rw [sourceCommonPairDomain_eq] at hcap
  letI := referenceWordMarkLaw_probability _ K (sourceReferenceIntensity m 14)
    (sourceReferenceIntensity_bounds m 14 hm0 (by norm_num) (by linarith)).1.le
    (hcap.trans (by norm_num))
  letI := finiteExcursionRecord_countable WordMark j
  letI := finiteRecordReferenceMeasure_probability hmarked μ inferInstance j
  have hh := disk_forest_reference_upper (Real.exp t) b
    (growingRecordRadius m j - 14) (Real.exp 1 * growingRecordRadius m j + 14)
    (by linarith) (by nlinarith [Real.exp_one_gt_two]) hfit hout
    (actualFiniteWordRecord (growingRecordEntrance b m 14)
      (growingRecordExit b m 14) (firstEntranceWordOfWord (growingRecordExit b m 14 0) K) j)
    1 (by norm_num) η (finiteRecordReferenceMeasure μ j)
    (fun y _ _ ↦ setHitProbability_le_one _ _ y)
    (by
      intro z hzlo hzhi r
      rw [finiteRecordReferenceMeasure_real_singleton]
      exact (hc b w hbw (show aR ≤ _ by omega) hrange j z r hzlo hzhi).2)
    1 (by norm_num) {rs | ∃ r ∈ s, rs = [r]} E
    (by rintro rs ⟨r, hr, rfl⟩; rfl)
    (by
      rintro rs ⟨r, hr, rfl⟩
      have herr := he b w hbw (show aE ≤ _ by omega) hrange WordMark r (hbar r hr)
      simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
        using herr)
  rw [independentForestLaw_single_root_event, finiteRecordReferenceMeasure_apply] at hh
  simpa only [Nat.sub_self, pow_zero, one_mul, Set.mem_setOf_eq, m, K, μ,
    growingRecordEntrance, growingRecordExit] using hh

end SRWTightness
