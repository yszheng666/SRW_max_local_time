import SRWTightness.SourceTerminalOrderedWordWide
import SRWTightness.SourceOrderedWordUniformUpper
import SRWTightness.HalfRadiusTerminalError
import SRWTightness.UniformProbabilityExponential

open MeasureTheory
namespace SRWTightness

/-- The full terminal exponential comparison holds throughout the half-radius range. -/
theorem source_terminal_ordered_word_all_radii (hP : PotentialKernelAsymptoticInput)
    (hHarm : PositiveHarmonicRelativeInput) :
    ∃ W M : ℝ, 0 ≤ W ∧ 128 ≤ M ∧ ∀ (m H a : ℝ),
      M ≤ m → 0 < a → 0 ≤ H → H ≤ m / 8 → a ≤ m / 2 →
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
  obtain ⟨W, M, hW, hM, hh⟩ := source_terminal_ordered_word_wide hP hHarm
  obtain ⟨c, T₁, hc, hT₁, hl⟩ := source_ordered_word_uniform_lower hP hHarm
  obtain ⟨U, T₂, hU, hT₂, hu⟩ := source_ordered_word_uniform_upper hP hHarm
  let A : ℝ := |Real.log c| + |Real.log U| + 1
  let W' : ℝ := max W (2 * A / Real.log 2)
  have hW' : 0 ≤ W' := hW.trans (le_max_left _ _)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨W', max M (max T₁ T₂), hW', hM.trans (le_max_left _ _), ?_⟩
  intro m H a hm ha hH hHm ham b z K hK hz hcap
  dsimp only
  intro s hs
  have hMm : M ≤ m := (le_max_left _ _).trans hm
  have hT₁m : T₁ ≤ m := (le_max_left _ _).trans ((le_max_right _ _).trans hm)
  have hT₂m : T₂ ≤ m := (le_max_right _ _).trans ((le_max_right _ _).trans hm)
  have hm128 : 128 ≤ m := hM.trans hMm
  have hm0 : 0 < m := by linarith
  have hlog : 0 ≤ Real.log (m / a) :=
    Real.log_nonneg ((one_le_div ha).mpr (by linarith))
  by_cases hsmall : a ≤ m / 4
  · have hp := hh m H a hMm ha hH hHm (by linarith) b z K hK hz hcap s hs
    have he : W * (a + 1) / m * Real.log (m / a) ≤
        W' * (a + 1) / m * Real.log (m / a) := by
      have h := mul_le_mul_of_nonneg_right (le_max_left W (2 * A / Real.log 2))
        (show 0 ≤ (a + 1) / m * Real.log (m / a) by positivity)
      calc
        _ = W * ((a + 1) / m * Real.log (m / a)) := by ring
        _ ≤ W' * ((a + 1) / m * Real.log (m / a)) := h
        _ = _ := by ring
    constructor
    · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith))
        measureReal_nonneg).trans hp.1
    · exact hp.2.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith))
        measureReal_nonneg)
  · have hlo := hl m H a hT₁m hH hHm ha.le ham b K hK z hz.1 hz.2
      (by linarith) s hs
    have hhi := hu m H a hT₂m hH hHm ha.le ham b K hK z hz.1 hz.2 hcap s hs
    have hx := half_radius_terminal_error m a hm0 ha (lt_of_not_ge hsmall).le ham
    have hw : 2 * A ≤ W' * Real.log 2 :=
      (div_le_iff₀ hlog2).mp (le_max_right W (2 * A / Real.log 2))
    have hprod := mul_le_mul_of_nonneg_left hx (show 0 ≤ 2 * W' by positivity)
    have hE : A ≤ 2 * (W' * (a + 1) / m * Real.log (m / a)) := by
      calc
        A ≤ 2 * W' * (Real.log 2 / 4) := by nlinarith [hw]
        _ ≤ 2 * W' * ((a + 1) / m * Real.log (m / a)) := hprod
        _ = _ := by ring
    apply uniform_probability_exponential _ _ c U _ measureReal_nonneg hc
      (by linarith : 0 < U) hlo hhi
    · exact (show |Real.log c| ≤ A by
        dsimp [A]; linarith [abs_nonneg (Real.log U)]).trans hE
    · exact (show |Real.log U| ≤ A by
        dsimp [A]; linarith [abs_nonneg (Real.log c)]).trans hE

end SRWTightness
