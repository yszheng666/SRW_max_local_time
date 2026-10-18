import SRWTightness.SourceCommonPairRecordComparison
import SRWTightness.SourceCommonPrefixErrorSmall
import SRWTightness.RecordReferenceEventMass

open MeasureTheory Filter
open scoped ENNReal
namespace SRWTightness

/-- Joint barrier-constrained common-prefix events obey a uniform reference probability comparison. -/
theorem source_common_prefix_event_upper (hinput : PotentialKernelAsymptoticInput)
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
        ((2 / Real.pi) * Real.log ((Real.exp 1 * m + 14) / (m - 14)))
      ∀ x : Site, growingRecordRadius m j - 14 - 1 ≤ Real.sqrt (normSq (x - b)) →
      Real.sqrt (normSq (x - b)) ≤ growingRecordRadius m j - 14 →
      ∀ s : Set (FiniteExcursionRecord (Mark K) j),
      (∀ r ∈ s, ∀ k : ℕ, 0 < k → k ≤ j →
        geometricGWHeight (finiteRecordPopulationList j r) k ≤
          4 + sourceBarrierSlope t * k -
            (min (k : ℝ) (sourceTotalTime t - k)) ^ (2 / 5 : ℝ)) →
      pathLaw {ω | actualFiniteWordRecord (growingRecordEntrance b m 14)
        (growingRecordExit b m 14) (wordOccupationMark K) j x
        (killedPathWord (growingRecordExit b m 14 j) x ω) ∈ s} ≤
      ENNReal.ofReal (Real.exp ε) * finiteRecordReferenceMass μ j s := by
  obtain ⟨B, W, hB, hW, hcompare⟩ := source_common_pair_record_comparison hinput
  filter_upwards [hcompare, source_common_prefix_error_small B W hB hW ε hε]
    with t hc he
  intro b w j hbw hρ ho hi hd
  dsimp only
  intro x hxl hxu s hbar
  let m := sourceCommonPairInnerRadius t j
  let K := sourceCommonPairObservation b w
  let μ := referenceMarkLaw (translateFinset b (diskFinset (Real.exp 1 * m + 14))) K
    ((2 / Real.pi) * Real.log ((Real.exp 1 * m + 14) / (m - 14)))
  have hh := actual_finite_record_event_comparison
    (growingRecordEntrance b m 14) (growingRecordExit b m 14) (wordOccupationMark K)
    j x (fun v ↦ μ.real {v})
    (fun _ ↦ 2 * (W * (2 * Real.sqrt (normSq (w - b)) + 1) / m *
      Real.log (m / (2 * Real.sqrt (normSq (w - b))))))
    (fun i ↦ 4 * (B * 14 / growingRecordRadius m i))
    (fun _ ↦ measureReal_nonneg) s ε
    (fun r hr ↦ (he _ j hρ ho hi hd (Mark K) r (hbar r hr)).le)
    (fun r _ ↦ hc b w j hbw hρ ho hi hd j x r hxl hxu)
  rw [← finiteRecordReferenceMass_subtype μ j s] at hh
  exact hh.2

end SRWTightness
