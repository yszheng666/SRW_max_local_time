import SRWTightness.SourceCommonPrefixEventComparison
import SRWTightness.SourceCommonLiteralPrefixError
import SRWTightness.SourceCommonSignedGeometry

open MeasureTheory Filter
open scoped ENNReal

namespace SRWTightness

/-- Actual joint common-prefix events satisfy the literal source logarithmic-error comparison. -/
theorem source_common_literal_event_comparison (hinput : PotentialKernelAsymptoticInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in atTop, ∀ (b w : Site) (j : ℕ), b ≠ w →
      (j : ℤ) = sourceSignedCommonPairLevel t (Real.sqrt (normSq (w - b))) →
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
      ENNReal.ofReal (Real.exp (-sourceCommonLiteralError C t j)) *
          finiteRecordReferenceMass μ j s ≤
        pathLaw {ω | actualFiniteWordRecord (growingRecordEntrance b m 14)
          (growingRecordExit b m 14) (wordOccupationMark K) j x
          (killedPathWord (growingRecordExit b m 14 j) x ω) ∈ s} ∧
      pathLaw {ω | actualFiniteWordRecord (growingRecordEntrance b m 14)
        (growingRecordExit b m 14) (wordOccupationMark K) j x
        (killedPathWord (growingRecordExit b m 14 j) x ω) ∈ s} ≤
      ENNReal.ofReal (Real.exp (sourceCommonLiteralError C t j)) *
        finiteRecordReferenceMass μ j s := by
  obtain ⟨B, W, hB, hW, hcompare⟩ := source_common_pair_record_comparison hinput
  let C₀ := 128 * B + 48 * Real.exp 1 * W
  have hC : 0 ≤ C₀ := by dsimp [C₀]; positivity
  refine ⟨C₀ + 1, by linarith, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ), hcompare,
    source_common_prefix_literal_error B W hB hW 1 (by norm_num)] with t ht hc he
  intro b w j hbw hj hd
  obtain ⟨hρ, ho, hi⟩ := source_common_signed_pair_geometry t b w j ht hbw hj
  dsimp only
  intro x hxl hxu s hbar
  let m := sourceCommonPairInnerRadius t j
  let K := sourceCommonPairObservation b w
  let μ := referenceMarkLaw (translateFinset b (diskFinset (Real.exp 1 * m + 14))) K
    ((2 / Real.pi) * Real.log ((Real.exp 1 * m + 14) / (m - 14)))
  have hmono : sourceCommonLiteralError C₀ t j ≤ sourceCommonLiteralError (C₀ + 1) t j := by
    unfold sourceCommonLiteralError
    apply mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : C₀ ≤ C₀ + 1) (sq_nonneg t))
    have hm := (sourceCommonPairInnerRadius_pos t j).le
    positivity
  have hh := actual_finite_record_event_comparison
    (growingRecordEntrance b m 14) (growingRecordExit b m 14) (wordOccupationMark K)
    j x (fun v ↦ μ.real {v})
    (fun _ ↦ 2 * (W * (2 * Real.sqrt (normSq (w - b)) + 1) / m *
      Real.log (m / (2 * Real.sqrt (normSq (w - b))))))
    (fun i ↦ 4 * (B * 14 / growingRecordRadius m i))
    (fun _ ↦ measureReal_nonneg) s (sourceCommonLiteralError (C₀ + 1) t j)
    (fun r hr ↦ ((he _ j hρ ho hj hd (Mark K) r (hbar r hr)).1).trans hmono)
    (fun r _ ↦ hc b w j hbw hρ ho hi hd j x r hxl hxu)
  rw [← finiteRecordReferenceMass_subtype μ j s] at hh
  exact hh

end SRWTightness
