import SRWTightness.SourceCommonPairRecordComparison
import SRWTightness.SourceCommonPrefixErrorSmall
import SRWTightness.DiskForestReferenceUpper
import SRWTightness.FiniteRecordReferenceMeasure
import SRWTightness.SingleRootReferenceEvent

open MeasureTheory Filter
open scoped ENNReal
namespace SRWTightness

/-- Origin-started single-root common-prefix events obey the reference upper comparison. -/
theorem source_common_origin_event_upper (hinput : PotentialKernelAsymptoticInput)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (j : ℕ), b ≠ w →
      1 ≤ Real.sqrt (normSq (w - b)) →
      Real.sqrt (normSq (w - b)) ≤ sourceRecordRadius (sourceLowerRadius t)
        (sourceRootDepth (Real.exp t) (sourceLowerRadius t)) 0 →
      j + sourceCommonPairGap t = sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      j + 1 ≤ sourceRootDepth (Real.exp t) (sourceLowerRadius t) →
      let m := sourceCommonPairInnerRadius t j
      let K := sourceCommonPairObservation b w
      let μ := referenceMarkLaw (translateFinset b (diskFinset (Real.exp 1 * m + 14))) K
        (sourceReferenceIntensity m 14)
      Real.sqrt (normSq b) + (Real.exp 1 * growingRecordRadius m j + 14) + 1 < Real.exp t →
      growingRecordRadius m j - 14 ≤ Real.sqrt (normSq b) →
      ∀ [MeasurableSpace (FiniteExcursionRecord (Mark K) j)]
        [MeasurableSingletonClass (FiniteExcursionRecord (Mark K) j)]
        [MeasurableSpace (List (FiniteExcursionRecord (Mark K) j))]
        [MeasurableSingletonClass (List (FiniteExcursionRecord (Mark K) j))],
      MarkedGWTreeInput (Mark K) →
      ∀ s : Set (FiniteExcursionRecord (Mark K) j),
      (∀ r ∈ s, ∀ k : ℕ, 0 < k → k ≤ j →
        geometricGWHeight (finiteRecordPopulationList j r) k ≤
          4 + sourceBarrierSlope t * k -
            (min (k : ℝ) (sourceTotalTime t - k)) ^ (2 / 5 : ℝ)) →
      pathLaw {ω | ∃ r ∈ s, killedChildRecords (diskFinset (Real.exp t))
        (growingRecordEntrance b m 14 j) (growingRecordExit b m 14 j) 0
        (actualFiniteWordRecord (growingRecordEntrance b m 14)
          (growingRecordExit b m 14) (wordOccupationMark K) j) ω = [r]} ≤
        ENNReal.ofReal (Real.exp ε) * finiteRecordReferenceMass μ j s := by
  obtain ⟨B, W, hB, hW, hcompare⟩ := source_common_pair_record_comparison hinput
  filter_upwards [hcompare, source_common_prefix_error_small B W hB hW ε hε,
    source_common_pair_observation_uniform, eventually_ge_atTop (sourceScaleThreshold 4)]
    with t hc he hg ht
  intro b w j hbw hρ ho hi hd
  dsimp only
  intro hfit hout inst₁ inst₂ inst₃ inst₄ hmarked s hbar
  let m := sourceCommonPairInnerRadius t j
  let K := sourceCommonPairObservation b w
  let μ := referenceMarkLaw (translateFinset b (diskFinset (Real.exp 1 * m + 14))) K
    (sourceReferenceIntensity m 14)
  let η := finiteRecordError (fun i ↦ 4 * (B * 14 / growingRecordRadius m i))
    (fun _ : Mark K ↦ 2 * (W * (2 * Real.sqrt (normSq (w - b)) + 1) / m *
      Real.log (m / (2 * Real.sqrt (normSq (w - b)))))) j
  have hm : 70 ≤ m := ((sourceScaleThreshold_conditions t 4 (by norm_num) ht).2.2.1).trans
    (sourceCommonPairInnerRadius_ge_lower t j hd)
  have hm0 : 0 < m := sourceCommonPairInnerRadius_pos t j
  have hrad := growingRecordRadius_ge_base m hm0.le j
  have hgeom := hg b w j hbw hi
  have hcap := source_terminal_capacity_half b m 14
    (2 * Real.sqrt (normSq (w - b))) K hgeom.1 hgeom.2.1 (by norm_num)
    (by linarith) (Finset.Subset.refl _) hgeom.2.2
  letI := referenceMarkLaw_isProbabilityMeasure _ K (sourceReferenceIntensity m 14)
    (sourceReferenceIntensity_bounds m 14 hm0 (by norm_num) (by linarith)).1.le
    (hcap.trans (by norm_num))
  letI := finiteExcursionRecord_countable (Mark K) j
  letI := finiteRecordReferenceMeasure_probability hmarked μ inferInstance j
  have hh := disk_forest_reference_upper (Real.exp t) b
    (growingRecordRadius m j - 14) (Real.exp 1 * growingRecordRadius m j + 14)
    (by linarith) (by nlinarith [Real.exp_one_gt_two]) hfit hout
    (actualFiniteWordRecord (growingRecordEntrance b m 14)
      (growingRecordExit b m 14) (wordOccupationMark K) j)
    1 (by norm_num) η (finiteRecordReferenceMeasure μ j)
    (fun y _ _ ↦ setHitProbability_le_one _ _ y)
    (by
      intro z hzlo hzhi r
      rw [finiteRecordReferenceMeasure_real_singleton]
      exact (hc b w j hbw hρ ho hi hd j z r hzlo hzhi).2)
    1 (by norm_num) {rs | ∃ r ∈ s, rs = [r]} ε
    (by rintro rs ⟨r, hr, rfl⟩; rfl)
    (by
      rintro rs ⟨r, hr, rfl⟩
      have herr := (he _ j hρ ho hi hd (Mark K) r (hbar r hr)).le
      simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] using herr)
  rw [independentForestLaw_single_root_event, finiteRecordReferenceMeasure_apply] at hh
  simpa only [Nat.sub_self, pow_zero, one_mul, Set.mem_setOf_eq, m, K, μ,
    growingRecordEntrance, growingRecordExit] using hh

end SRWTightness
