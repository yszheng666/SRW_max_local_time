import SRWTightness.SourceUniformEntranceAtoms
import SRWTightness.SourceTerminalZeroMass
import SRWTightness.OrderedWordUniformLower

open MeasureTheory
namespace SRWTightness

/-- The full actual ordered terminal law has a fixed positive lower comparison. -/
theorem source_ordered_word_uniform_lower (hP : PotentialKernelAsymptoticInput)
    (hHarm : PositiveHarmonicRelativeInput) :
    ∃ c T : ℝ, 0 < c ∧ 128 ≤ T ∧ ∀ (m H a : ℝ), T ≤ m →
      0 ≤ H → H ≤ m / 8 → 0 ≤ a → a ≤ m / 2 →
      ∀ (b : Site) (K : Finset Site), K ⊆ translateFinset b (diskFinset a) →
      ∀ z : Site, m - H - 1 ≤ Real.sqrt (normSq (z - b)) →
      Real.sqrt (normSq (z - b)) ≤ m - H + 1 →
      let D := translateFinset b (diskFinset (Real.exp 1 * m + H))
      let α := (2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H))
      α * capacity D K ≤ 1 → ∀ s : Set WordMark, MeasurableSet s →
      c * (referenceWordMarkLaw D K α).real s ≤ (firstEntranceWordMarkLaw D K z).real s := by
  obtain ⟨c, U, T, hc, hU, hT, hh⟩ := source_uniform_entrance_atoms hP hHarm
  obtain ⟨c₀, T₀, hc₀, hT₀, hz⟩ := source_terminal_zero_mass hP
  refine ⟨min c c₀, max T T₀, lt_min hc hc₀, hT.trans (le_max_left _ _), ?_⟩
  intro m H a hm hH hHm ha ham b K hK z hzlo hzhi
  dsimp only
  intro hcap s hs
  have hTm : T ≤ m := (le_max_left _ _).trans hm
  have hT₀m : T₀ ≤ m := (le_max_right _ _).trans hm
  have hm0 : 0 < m := by linarith [hT.trans hTm]
  have hα : 0 ≤ (2 / Real.pi) * Real.log ((Real.exp 1 * m + H) / (m - H)) :=
    (by positivity : 0 ≤ (2 / Real.pi : ℝ)).trans
      (source_terminal_alpha_lower m H hm0 hH (by linarith))
  apply firstEntranceWordMark_event_uniform_lower _ K z _ _ hα (lt_min hc hc₀).le hcap
  · have h := (min_le_right c c₀).trans (hz m H a hT₀m hH hHm ha ham b K hK z hzlo hzhi)
    rwa [firstEntranceWordMarkLaw_none] at h
  · intro v hv
    exact (mul_le_mul_of_nonneg_right (min_le_left c c₀)
      (mul_nonneg hα (equilibriumMeasure_nonneg _ _ _))).trans
        (hh m H a hTm hH hHm ha ham b K hK z hzlo hzhi v hv).1
  · exact hs

end SRWTightness
