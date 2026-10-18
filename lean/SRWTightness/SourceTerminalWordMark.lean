import SRWTightness.SourceTerminalMarkComparison
import SRWTightness.RelativeProbabilityExponential
import SRWTightness.WordOccupationMark

open MeasureTheory

namespace SRWTightness

/-- Source terminal marks extracted from actual words satisfy the exponential record base bound. -/
theorem source_terminal_word_mark_exponential (hinput : PotentialKernelAsymptoticInput) :
    ∃ W M : ℝ, 0 ≤ W ∧ 8 ≤ M ∧ ∀ (m H a : ℝ),
      M ≤ m → 0 < a → 0 ≤ H → H ≤ m / 2 → 2 * a < m - H - 2 →
      ∀ (b z : Site) (K : Finset Site), K ⊆ translateFinset b (diskFinset a) →
        (m - H - 1 ≤ Real.sqrt (normSq (z - b)) ∧
          Real.sqrt (normSq (z - b)) ≤ m - H + 1) →
        ((2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H))) *
          capacity (translateFinset b (diskFinset (Real.exp 1 * m + H))) K ≤ 1 / 2 →
        W * (a + 1) / m * Real.log (m / a) ≤ 1 / 2 →
        ∀ s : Set (Mark K), MeasurableSet s →
        Real.exp (-(2 * (W * (a + 1) / m * Real.log (m / a)))) *
          (referenceMarkLaw (translateFinset b (diskFinset (Real.exp 1 * m + H))) K
            ((2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H)))).real s ≤
          pathLaw.real {ω | wordOccupationMark K z
            (killedPathWord (translateFinset b (diskFinset (Real.exp 1 * m + H))) z ω) ∈ s} ∧
        pathLaw.real {ω | wordOccupationMark K z
            (killedPathWord (translateFinset b (diskFinset (Real.exp 1 * m + H))) z ω) ∈ s} ≤
          Real.exp (2 * (W * (a + 1) / m * Real.log (m / a))) *
          (referenceMarkLaw (translateFinset b (diskFinset (Real.exp 1 * m + H))) K
            ((2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H)))).real s := by
  obtain ⟨W, M, hW, hM, hh⟩ := source_terminal_mark_event_comparison hinput
  refine ⟨W, M, hW, hM, ?_⟩
  intro m H a hm ha hH hHm hsep b z K hK hz hcap hsmall s hs
  have hm0 : 0 < m := by linarith
  have ht : 0 ≤ Real.log (m / a) :=
    (Real.log_pos ((one_lt_div ha).mpr (by linarith))).le
  rw [wordOccupationMark_event_probability _ K z s hs]
  exact relative_probability_exponential _ _ _ measureReal_nonneg (by positivity) hsmall
    (hh m H a hm ha hH hHm hsep b z K hK hz hcap s hs)

end SRWTightness
