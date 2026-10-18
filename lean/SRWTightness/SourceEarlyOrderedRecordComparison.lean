import SRWTightness.GrowingOrderedRecordComparison
import SRWTightness.SourceEarlyOrderedConditions

open MeasureTheory Filter

namespace SRWTightness

/-- The ordered record comparison on the original early distance-dependent common scale. -/
theorem source_early_ordered_record_comparison (hinput : PotentialKernelAsymptoticInput) :
    ∃ B W : ℝ, 0 ≤ B ∧ 0 ≤ W ∧
      ∃ Jmin : ℕ, ∀ J₀ : ℕ, Jmin ≤ J₀ → ∃ a₀ : ℕ, 1 ≤ a₀ ∧
      ∀ᶠ t : ℝ in atTop, ∀ b w : Site, b ≠ w →
      a₀ ≤ sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) →
      sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b))) <
        sourceCoarseLowerLevel t + sourceCommonPairGap t →
      let a := sourceCommonPairDistanceIndex t (Real.sqrt (normSq (w - b)))
      let j := a - sourceEarlyDistanceGap a J₀
      let m := sourceCommonPairInnerRadius t j
      let R := 2 * Real.sqrt (normSq (w - b))
      let K := sourceCommonPairObservation b w
      let η : WordMark → ℝ := fun _ ↦ 2 * (W * (R + 1) / m * Real.log (m / R))
      let Q : WordMark → ℝ := fun v ↦
        (referenceWordMarkLaw (translateFinset b (diskFinset (Real.exp 1 * m + 14))) K
          ((2 / Real.pi) * Real.log ((Real.exp 1 * m + 14) / (m - 14)))).real {v}
      ∀ n x (r : FiniteExcursionRecord WordMark n),
      growingRecordRadius m n - 14 - 1 ≤ Real.sqrt (normSq (x - b)) →
      Real.sqrt (normSq (x - b)) ≤ growingRecordRadius m n - 14 →
      Real.exp (-finiteRecordError (fun j ↦ 4 * (B * 14 / growingRecordRadius m j)) η n r) *
          finiteRecordReferenceWeight Q n r ≤
        pathLaw.real {ω | actualFiniteWordRecord (growingRecordEntrance b m 14)
          (growingRecordExit b m 14) (firstEntranceWordOfWord (growingRecordExit b m 14 0) K) n x
          (killedPathWord (growingRecordExit b m 14 n) x ω) = r} ∧
      pathLaw.real {ω | actualFiniteWordRecord (growingRecordEntrance b m 14)
          (growingRecordExit b m 14) (firstEntranceWordOfWord (growingRecordExit b m 14 0) K) n x
          (killedPathWord (growingRecordExit b m 14 n) x ω) = r} ≤
        Real.exp (finiteRecordError (fun j ↦ 4 * (B * 14 / growingRecordRadius m j)) η n r) *
          finiteRecordReferenceWeight Q n r := by
  obtain ⟨B, W, T, M, hB, hW, hT, hM, hh⟩ :=
    growing_ordered_record_probability_comparison hinput
  obtain ⟨Jmin, hc⟩ := source_early_ordered_conditions B W T M hB hW
  refine ⟨B, W, hB, hW, Jmin, ?_⟩
  intro J₀ hJ₀
  obtain ⟨a₀, ha₀, hc⟩ := hc J₀ hJ₀
  refine ⟨a₀, ha₀, ?_⟩
  filter_upwards [hc] with t ht
  intro b w hbw ha hrange
  dsimp only
  obtain ⟨hm112, hmT, hmM, hmB, hR, hsep, hcap, herr⟩ := ht b w hbw ha hrange
  rw [sourceCommonPairDomain_eq] at hcap
  exact hh b _ 14 _ (sourceCommonPairObservation b w) (by norm_num)
    (by norm_num; exact hm112) hmT hmM hmB hR hsep (Finset.Subset.refl _) hcap herr

end SRWTightness
