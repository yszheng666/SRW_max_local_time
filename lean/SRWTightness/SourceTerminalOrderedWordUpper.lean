import SRWTightness.SourceTerminalOrderedWordComparison
import SRWTightness.RelativeProbabilityUpper

open MeasureTheory
namespace SRWTightness

/-- Ordered terminal events satisfy an exponential upper bound at every relative-error size. -/
theorem source_terminal_ordered_word_upper (hinput : PotentialKernelAsymptoticInput) :
    ∃ W M : ℝ, 0 ≤ W ∧ 8 ≤ M ∧ ∀ (m H a : ℝ),
      M ≤ m → 0 < a → 0 ≤ H → H ≤ m / 2 → 2 * a < m - H - 2 →
      ∀ (b z : Site) (K : Finset Site), K ⊆ translateFinset b (diskFinset a) →
        (m - H - 1 ≤ Real.sqrt (normSq (z - b)) ∧
          Real.sqrt (normSq (z - b)) ≤ m - H + 1) →
        ((2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H))) *
          capacity (translateFinset b (diskFinset (Real.exp 1 * m + H))) K ≤ 1 / 2 →
        let D := translateFinset b (diskFinset (Real.exp 1 * m + H))
        let α := (2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H))
        let ε := W * (a + 1) / m * Real.log (m / a)
        ∀ s : Set WordMark, MeasurableSet s →
          (firstEntranceWordMarkLaw D K z).real s ≤
            Real.exp ε * (referenceWordMarkLaw D K α).real s := by
  obtain ⟨W, M, hW, hM, hh⟩ := source_terminal_ordered_word_event_comparison hinput
  refine ⟨W, M, hW, hM, ?_⟩
  intro m H a hm ha hH hHm hsep b z K hK hz hcap
  dsimp only
  intro s hs
  exact relative_probability_exponential_upper _ _ _ measureReal_nonneg
    (hh m H a hm ha hH hHm hsep b z K hK hz hcap s hs)

end SRWTightness
