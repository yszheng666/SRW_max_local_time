import SRWTightness.OrderedWordRelativeComparison
import SRWTightness.SourceEntranceAllRadii
import SRWTightness.RelativeProbabilityExponential

open MeasureTheory

namespace SRWTightness

/-- Uniform geometric comparison of actual first-entry ordered marks and their reference law. -/
theorem source_terminal_ordered_word_event_comparison (hinput : PotentialKernelAsymptoticInput) :
    ∃ W M : ℝ, 0 ≤ W ∧ 8 ≤ M ∧ ∀ (m H a : ℝ),
      M ≤ m → 0 < a → 0 ≤ H → H ≤ m / 2 → 2 * a < m - H - 2 →
      ∀ (b z : Site) (K : Finset Site), K ⊆ translateFinset b (diskFinset a) →
        (m - H - 1 ≤ Real.sqrt (normSq (z - b)) ∧
          Real.sqrt (normSq (z - b)) ≤ m - H + 1) →
        ((2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H))) *
          capacity (translateFinset b (diskFinset (Real.exp 1 * m + H))) K ≤ 1 / 2 →
        ∀ s : Set WordMark, MeasurableSet s →
        |(firstEntranceWordMarkLaw
            (translateFinset b (diskFinset (Real.exp 1 * m + H))) K z).real s -
          (referenceWordMarkLaw (translateFinset b (diskFinset (Real.exp 1 * m + H))) K
            ((2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H)))).real s| ≤
          (W * (a + 1) / m * Real.log (m / a)) *
            (referenceWordMarkLaw (translateFinset b (diskFinset (Real.exp 1 * m + H))) K
              ((2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H)))).real s := by
  obtain ⟨W, M, hW, hM, hh⟩ := source_entrance_all_positive_radii hinput
  refine ⟨W, M, hW, hM, ?_⟩
  intro m H a hm ha hH hHm hsep b z K hK hz hcap s hs
  have hm0 : 0 < m := by linarith
  have ht : 0 ≤ Real.log (m / a) :=
    (Real.log_pos ((one_lt_div ha).mpr (by linarith))).le
  have hα : 0 ≤ (2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H)) :=
    le_trans (by positivity) (source_terminal_alpha_lower m H hm0 hH (by linarith))
  exact firstEntranceWordMark_event_relative_comparison _ K z _ _ hα (by positivity) hcap
    (hh m H a hm ha hH hHm hsep b z K hK hz) s hs

/-- The source entrance error gives the exponential comparison needed for ordered records. -/
theorem source_terminal_ordered_word_exponential (hinput : PotentialKernelAsymptoticInput) :
    ∃ W M : ℝ, 0 ≤ W ∧ 8 ≤ M ∧ ∀ (m H a : ℝ),
      M ≤ m → 0 < a → 0 ≤ H → H ≤ m / 2 → 2 * a < m - H - 2 →
      ∀ (b z : Site) (K : Finset Site), K ⊆ translateFinset b (diskFinset a) →
        (m - H - 1 ≤ Real.sqrt (normSq (z - b)) ∧
          Real.sqrt (normSq (z - b)) ≤ m - H + 1) →
        ((2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H))) *
          capacity (translateFinset b (diskFinset (Real.exp 1 * m + H))) K ≤ 1 / 2 →
        W * (a + 1) / m * Real.log (m / a) ≤ 1 / 2 →
        let D := translateFinset b (diskFinset (Real.exp 1 * m + H))
        let α := (2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H))
        let ε := W * (a + 1) / m * Real.log (m / a)
        ∀ s : Set WordMark, MeasurableSet s →
          Real.exp (-(2 * ε)) * (referenceWordMarkLaw D K α).real s ≤
            (firstEntranceWordMarkLaw D K z).real s ∧
          (firstEntranceWordMarkLaw D K z).real s ≤
            Real.exp (2 * ε) * (referenceWordMarkLaw D K α).real s := by
  obtain ⟨W, M, hW, hM, hh⟩ := source_terminal_ordered_word_event_comparison hinput
  refine ⟨W, M, hW, hM, ?_⟩
  intro m H a hm ha hH hHm hsep b z K hK hz hcap hsmall
  dsimp only
  intro s hs
  have hm0 : 0 < m := by linarith
  have ht : 0 ≤ Real.log (m / a) :=
    (Real.log_pos ((one_lt_div ha).mpr (by linarith))).le
  exact relative_probability_exponential _ _ _ measureReal_nonneg (by positivity) hsmall
    (hh m H a hm ha hH hHm hsep b z K hK hz hcap s hs)

end SRWTightness
