import SRWTightness.SourceEarlyOrderedRecordComparison
import SRWTightness.SourceEarlyCommonPrefixError

open MeasureTheory Filter

namespace SRWTightness

/-- The early prefix barrier gives a uniform constant in the ordered record comparison. -/
theorem source_early_ordered_prefix_comparison (hinput : PotentialKernelAsymptoticInput) :
    ∃ B W : ℝ, 0 ≤ B ∧ 0 ≤ W ∧
      ∃ Jmin : ℕ, ∀ J₀ : ℕ, Jmin ≤ J₀ → ∃ a₀ : ℕ, 1 ≤ a₀ ∧
      ∀ᶠ t : ℝ in atTop, ∀ b w : Site, b ≠ w →
      a₀ ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) <
        sourceCoarseLowerLevel t + sourceCommonPairGap t →
      let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
      let j := a - sourceEarlyDistanceGap a J₀
      let m := sourceCommonPairInnerRadius t j
      let K := sourceCommonPairObservation b w
      let Q : WordMark → ℝ := fun v ↦
        (referenceWordMarkLaw (translateFinset b (diskFinset (Real.exp 1 * m + 14))) K
          ((2 / Real.pi) * Real.log ((Real.exp 1 * m + 14) / (m - 14)))).real {v}
      ∀ x (r : FiniteExcursionRecord WordMark j),
      (∀ k : ℕ, 0 < k → k ≤ j →
        geometricGWHeight (finiteRecordPopulationList j r) k ≤
          4 + sourceBarrierSlope t * k -
            (min (k : ℝ) (sourceTotalTime t - k)) ^ (2 / 5 : ℝ)) →
      growingRecordRadius m j - 14 - 1 ≤ Real.sqrt (normSq (x - b)) →
      Real.sqrt (normSq (x - b)) ≤ growingRecordRadius m j - 14 →
      Real.exp (-(57 * (128 * B + 48 * Real.exp 1 * W))) *
          finiteRecordReferenceWeight Q j r ≤
        pathLaw.real {ω | actualFiniteWordRecord (growingRecordEntrance b m 14)
          (growingRecordExit b m 14) (firstEntranceWordOfWord (growingRecordExit b m 14 0) K) j x
          (killedPathWord (growingRecordExit b m 14 j) x ω) = r} ∧
      pathLaw.real {ω | actualFiniteWordRecord (growingRecordEntrance b m 14)
          (growingRecordExit b m 14) (firstEntranceWordOfWord (growingRecordExit b m 14 0) K) j x
          (killedPathWord (growingRecordExit b m 14 j) x ω) = r} ≤
        Real.exp (57 * (128 * B + 48 * Real.exp 1 * W)) *
          finiteRecordReferenceWeight Q j r := by
  obtain ⟨B, W, hB, hW, JR, hr⟩ := source_early_ordered_record_comparison hinput
  obtain ⟨JE, he⟩ := source_early_common_prefix_error B W hB hW
  refine ⟨B, W, hB, hW, max JR JE, ?_⟩
  intro J₀ hJ₀
  obtain ⟨aR, haR, hr⟩ := hr J₀ ((le_max_left _ _).trans hJ₀)
  obtain ⟨aE, haE, he⟩ := he J₀ ((le_max_right _ _).trans hJ₀)
  refine ⟨aR + aE, by omega, ?_⟩
  filter_upwards [hr, he] with t hr he
  intro b w hbw ha hrange
  dsimp only
  intro x r hbar hxl hxu
  have hrecord := hr b w hbw (show aR ≤ _ by omega) hrange _ x r hxl hxu
  have herror := he b w hbw (show aE ≤ _ by omega) hrange WordMark r hbar
  constructor
  · exact (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (neg_le_neg herror)) (finiteRecordReferenceWeight_nonneg _
        (fun _ ↦ measureReal_nonneg) _ r)).trans hrecord.1
  · exact hrecord.2.trans (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr herror) (finiteRecordReferenceWeight_nonneg _
        (fun _ ↦ measureReal_nonneg) _ r))

end SRWTightness
