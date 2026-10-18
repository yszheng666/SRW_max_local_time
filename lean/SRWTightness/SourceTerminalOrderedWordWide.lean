import SRWTightness.SourceOrderedWordUniformLower
import SRWTightness.SourceTerminalOrderedWordComparison
import SRWTightness.RelativeProbabilityWideExponential

open MeasureTheory
namespace SRWTightness

/-- The full terminal exponential comparison holds without a relative-error smallness premise. -/
theorem source_terminal_ordered_word_wide (hP : PotentialKernelAsymptoticInput)
    (hHarm : PositiveHarmonicRelativeInput) :
    ∃ W M : ℝ, 0 ≤ W ∧ 128 ≤ M ∧ ∀ (m H a : ℝ),
      M ≤ m → 0 < a → 0 ≤ H → H ≤ m / 8 → 2 * a < m - H - 2 →
      ∀ (b z : Site) (K : Finset Site), K ⊆ translateFinset b (diskFinset a) →
        (m - H - 1 ≤ Real.sqrt (normSq (z - b)) ∧
          Real.sqrt (normSq (z - b)) ≤ m - H + 1) →
        ((2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H))) *
          capacity (translateFinset b (diskFinset (Real.exp 1 * m + H))) K ≤ 1 / 2 →
        let D := translateFinset b (diskFinset (Real.exp 1 * m + H))
        let α := (2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H))
        let ε := W * (a + 1) / m * Real.log (m / a)
        ∀ s : Set WordMark, MeasurableSet s →
          Real.exp (-(2 * ε)) * (referenceWordMarkLaw D K α).real s ≤
            (firstEntranceWordMarkLaw D K z).real s ∧
          (firstEntranceWordMarkLaw D K z).real s ≤
            Real.exp (2 * ε) * (referenceWordMarkLaw D K α).real s := by
  obtain ⟨W, M, hW, hM, hh⟩ := source_terminal_ordered_word_event_comparison hP
  obtain ⟨c, T, hc, hT, hl⟩ := source_ordered_word_uniform_lower hP hHarm
  let W' : ℝ := (1 + |Real.log c|) * W
  refine ⟨W', max M T, by dsimp [W']; positivity, hT.trans (le_max_right _ _), ?_⟩
  intro m H a hm ha hH hHm hsep b z K hK hz hcap
  dsimp only
  intro s hs
  have hMm : M ≤ m := (le_max_left _ _).trans hm
  have hTm : T ≤ m := (le_max_right _ _).trans hm
  have hm0 : 0 < m := by linarith [hM.trans hMm]
  have hlog : 0 ≤ Real.log (m / a) :=
    (Real.log_pos ((one_lt_div ha).mpr (by linarith))).le
  have hr := hh m H a hMm ha hH (by linarith) hsep b z K hK hz hcap s hs
  have hlow := hl m H a hTm hH hHm ha.le (by linarith) b K hK z hz.1 hz.2
    (by linarith : ((2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H))) *
      capacity (translateFinset b (diskFinset (Real.exp 1 * m + H))) K ≤ 1) s hs
  have hp := relative_probability_wide_exponential _ _
    (W * (a + 1) / m * Real.log (m / a)) c measureReal_nonneg (by positivity) hc hr hlow
  have he : 2 * (W' * (a + 1) / m * Real.log (m / a)) =
      2 * (1 + |Real.log c|) * (W * (a + 1) / m * Real.log (m / a)) := by
    dsimp [W']
    ring
  rw [he]
  exact hp

end SRWTightness
