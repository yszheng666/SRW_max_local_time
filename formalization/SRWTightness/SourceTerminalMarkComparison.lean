import SRWTightness.ActualMarkEventComparison
import SRWTightness.SourceEntranceAllRadii

open MeasureTheory

namespace SRWTightness

/-- Uniform comparison of actual terminal occupation records with reference marks, including zero. -/
theorem source_terminal_mark_event_comparison (hinput : PotentialKernelAsymptoticInput) :
    ∃ W M : ℝ, 0 ≤ W ∧ 8 ≤ M ∧ ∀ (m H a : ℝ),
      M ≤ m → 0 < a → 0 ≤ H → H ≤ m / 2 → 2 * a < m - H - 2 →
      ∀ (b z : Site) (K : Finset Site), K ⊆ translateFinset b (diskFinset a) →
        (m - H - 1 ≤ Real.sqrt (normSq (z - b)) ∧
          Real.sqrt (normSq (z - b)) ≤ m - H + 1) →
        ((2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H))) *
          capacity (translateFinset b (diskFinset (Real.exp 1 * m + H))) K ≤ 1 / 2 →
        ∀ s : Set (Mark K), MeasurableSet s →
        |(killedMarkLaw (translateFinset b (diskFinset (Real.exp 1 * m + H))) K z).real s -
          (referenceMarkLaw (translateFinset b (diskFinset (Real.exp 1 * m + H))) K
            ((2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H)))).real s| ≤
          (W * (a + 1) / m * Real.log (m / a)) *
            (referenceMarkLaw (translateFinset b (diskFinset (Real.exp 1 * m + H))) K
              ((2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H)))).real s := by
  obtain ⟨W, M, hW, hM, hh⟩ := source_entrance_all_positive_radii hinput
  refine ⟨W, M, hW, hM, ?_⟩
  intro m H a hm ha hH hHm hsep b z K hK hz hcap s hs
  have hm0 : 0 < m := by linarith
  have ht : 0 ≤ Real.log (m / a) :=
    (Real.log_pos ((one_lt_div ha).mpr (by linarith))).le
  have hα : 0 ≤ (2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H)) :=
    le_trans (by positivity) (source_terminal_alpha_lower m H hm0 hH (by linarith))
  exact actual_mark_event_relative_comparison _ K z _ _ hα (by positivity) hcap
    (hh m H a hm ha hH hHm hsep b z K hK hz) s hs

end SRWTightness
