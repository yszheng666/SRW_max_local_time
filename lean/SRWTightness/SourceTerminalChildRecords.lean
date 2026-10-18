import SRWTightness.SourceBufferedRecordProbability
import SRWTightness.SourceTerminalWordMark

open MeasureTheory

namespace SRWTightness

/-- Actual ordered terminal child marks have the geometric product reference weight. -/
theorem source_terminal_child_records_comparison (hinput : PotentialKernelAsymptoticInput) :
    ∃ B W T M : ℝ, 0 ≤ B ∧ 0 ≤ W ∧ 2 ≤ T ∧ 8 ≤ M ∧
      ∀ (b : Site) (ρ H a : ℝ) (K : Finset Site),
      1 ≤ H → 8 * H ≤ ρ → T ≤ ρ - H → M ≤ ρ →
      B * H / ρ ≤ 1 / 4 → 0 < a → 2 * a < ρ - H - 2 →
      K ⊆ translateFinset b (diskFinset a) →
      ((2 / Real.pi) * Real.log ((Real.exp 1 * ρ + H) / (ρ - H))) *
        capacity (translateFinset b (diskFinset (Real.exp 1 * ρ + H))) K ≤ 1 / 2 →
      W * (a + 1) / ρ * Real.log (ρ / a) ≤ 1 / 2 →
      let η : Mark K → ℝ := fun _ ↦ 2 * (W * (a + 1) / ρ * Real.log (ρ / a))
      let Q : Mark K → ℝ := fun r ↦
        (referenceMarkLaw (translateFinset b (diskFinset (Real.exp 1 * ρ + H))) K
          ((2 / Real.pi) * Real.log ((Real.exp 1 * ρ + H) / (ρ - H)))).real {r}
      ∀ rs x, x ∈ bufferedRecordMiddle b ρ H →
        Real.exp (-orderedRecordError (4 * (B * H / ρ)) η rs) *
          orderedReferenceWeight Q rs ≤
          pathLaw.real {ω | killedChildRecords
            (translateFinset b (diskFinset (Real.exp 2 * ρ + H)))
            (translateFinset b (diskFinset (ρ - H)))
            (translateFinset b (diskFinset (Real.exp 1 * ρ + H))) x
            (wordOccupationMark K) ω = rs} ∧
        pathLaw.real {ω | killedChildRecords
            (translateFinset b (diskFinset (Real.exp 2 * ρ + H)))
            (translateFinset b (diskFinset (ρ - H)))
            (translateFinset b (diskFinset (Real.exp 1 * ρ + H))) x
            (wordOccupationMark K) ω = rs} ≤
          Real.exp (orderedRecordError (4 * (B * H / ρ)) η rs) *
            orderedReferenceWeight Q rs := by
  obtain ⟨W, M, hW, hM, hmark⟩ := source_terminal_word_mark_exponential hinput
  obtain ⟨B, T, hB, hT, hrecord⟩ :=
    source_buffered_half_probabilities hinput
  refine ⟨B, W, T, M, hB, hW, hT, hM, ?_⟩
  intro b ρ H a K hH hρ hTρ hMρ hsmall ha hsep hK hcap herr
  dsimp only
  apply buffered_record_probability_comparison b ρ H hH hρ (wordOccupationMark K)
    (B * H / ρ) (div_nonneg (mul_nonneg hB (by linarith)) (by linarith)) hsmall
  · intro x hx
    exact (hrecord ρ H hH hρ hTρ b x hx).2
  · intro r
    exact measureReal_nonneg
  · intro z hzl hzu r
    simpa only [Set.mem_singleton_iff] using
      hmark ρ H a hMρ ha (by linarith) (by linarith) hsep b z K hK
        ⟨hzl, by linarith⟩ hcap herr {r} (measurableSet_singleton r)

end SRWTightness
