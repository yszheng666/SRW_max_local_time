import SRWTightness.SourceUniformEntranceAtoms
import SRWTightness.OrderedWordUniformUpper

open MeasureTheory
namespace SRWTightness

/-- The full terminal law has a uniform upper comparison throughout the half-radius range. -/
theorem source_ordered_word_uniform_upper (hP : PotentialKernelAsymptoticInput)
    (hHarm : PositiveHarmonicRelativeInput) :
    ∃ U T : ℝ, 2 ≤ U ∧ 128 ≤ T ∧ ∀ (m H a : ℝ), T ≤ m →
      0 ≤ H → H ≤ m / 8 → 0 ≤ a → a ≤ m / 2 →
      ∀ (b : Site) (K : Finset Site), K ⊆ translateFinset b (diskFinset a) →
      ∀ z : Site, m - H - 1 ≤ Real.sqrt (normSq (z - b)) →
      Real.sqrt (normSq (z - b)) ≤ m - H + 1 →
      let D := translateFinset b (diskFinset (Real.exp 1 * m + H))
      let α := (2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H))
      α * capacity D K ≤ 1 / 2 → ∀ s : Set WordMark, MeasurableSet s →
      (firstEntranceWordMarkLaw D K z).real s ≤ U * (referenceWordMarkLaw D K α).real s := by
  obtain ⟨c, U, T, hc, hU, hT, hh⟩ := source_uniform_entrance_atoms hP hHarm
  refine ⟨max U 2, T, le_max_right _ _, hT, ?_⟩
  intro m H a hm hH hHm ha ham b K hK z hzlo hzhi
  dsimp only
  intro hcap s hs
  have hm0 : 0 < m := by linarith [hT.trans hm]
  have hα : 0 ≤ (2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H)) :=
    (by positivity : 0 ≤ (2 / Real.pi : ℝ)).trans
      (source_terminal_alpha_lower m H hm0 hH (by linarith))
  apply firstEntranceWordMark_event_uniform_upper _ K z _ _ hα (by linarith)
  · have hmass := competing_entrance_exit_mass
      (translateFinset b (diskFinset (Real.exp 1 * m + H))) K z
    have hnon : 0 ≤ (competingEntranceLaw
      (translateFinset b (diskFinset (Real.exp 1 * m + H))) K z).real Set.univ :=
      measureReal_nonneg
    have hhalf : (1 / 2 : ℝ) ≤ 1 -
        ((2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H))) *
          capacity (translateFinset b (diskFinset (Real.exp 1 * m + H))) K := by linarith
    have hp := mul_le_mul_of_nonneg_left hhalf
      (show 0 ≤ max U 2 by exact le_trans (by norm_num) (le_max_right _ _))
    linarith [le_max_right U (2 : ℝ)]
  · intro v hv
    exact (hh m H a hm hH hHm ha ham b K hK z hzlo hzhi v hv).2.trans
      (mul_le_mul_of_nonneg_right (le_max_left U 2)
        (mul_nonneg hα (equilibriumMeasure_nonneg _ _ _)))
  · exact hs

end SRWTightness
