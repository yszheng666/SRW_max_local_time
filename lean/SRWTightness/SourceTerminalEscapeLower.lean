import SRWTightness.IntermediateEscapeLower
import Mathlib.Analysis.Complex.ExponentialBounds

namespace SRWTightness

/-- Uniform source escape lower bound on the intermediate comparison boundary. -/
theorem source_terminal_escape_lower (hinput : PotentialKernelAsymptoticInput) :
    ∃ c T : ℝ, 0 < c ∧ 2 ≤ T ∧ ∀ (m H a : ℝ), T ≤ a → 2 * a < m →
      0 ≤ H → H ≤ m / 2 → ∀ (b x : Site) (K : Finset Site),
        K ⊆ translateFinset b (diskFinset a) →
        (3 * a / 2 ≤ Real.sqrt (normSq (x - b)) ∧
          Real.sqrt (normSq (x - b)) ≤ 3 * a / 2 + 1) →
        c / Real.log (m / a) ≤
          1 - setHitProbability (translateFinset b (diskFinset (Real.exp 1 * m + H))) K x := by
  obtain ⟨c, T, hc, hT, hh⟩ := intermediate_escape_lower hinput
  refine ⟨c / 3, T, by positivity, hT, ?_⟩
  intro m H a ha ham hH hHm b x K hK hx
  have ha0 : 0 < a := by linarith
  have hm0 : 0 < m := by linarith
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hR : a < Real.exp 1 * m + H := by nlinarith
  have hR0 : 0 < Real.exp 1 * m + H := by nlinarith
  have hR4 : Real.exp 1 * m + H ≤ 4 * m := by nlinarith [Real.exp_one_lt_three]
  have hxu : normSq (x - b) < (Real.exp 1 * m + H) ^ 2 := by
    have hs := Real.sq_sqrt (normSq_nonneg (x - b))
    have hn := Real.sqrt_nonneg (normSq (x - b))
    have hupper : Real.sqrt (normSq (x - b)) < Real.exp 1 * m + H := by nlinarith [hx.2]
    nlinarith
  have hlower := hh a (Real.exp 1 * m + H) ha hR b x K hK hx.1 hxu
  have hma : 2 < m / a := (lt_div_iff₀ ha0).mpr ham
  have hlog : 0 < Real.log (m / a) := Real.log_pos (by linarith)
  have hden : 0 < Real.log ((Real.exp 1 * m + H) / a) :=
    Real.log_pos ((one_lt_div ha0).mpr hR)
  have h2 : Real.log 2 ≤ Real.log (m / a) := Real.log_le_log (by norm_num) hma.le
  have hupper : Real.log ((Real.exp 1 * m + H) / a) ≤ 3 * Real.log (m / a) := by
    have hl := Real.log_le_log (div_pos hR0 ha0)
      (div_le_div_of_nonneg_right hR4 ha0.le)
    rw [show 4 * m / a = 4 * (m / a) by ring,
      Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (div_ne_zero hm0.ne' ha0.ne')] at hl
    have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      ring
    rw [h4] at hl
    linarith
  refine le_trans ?_ hlower
  apply (div_le_div_iff₀ hlog hden).mpr
  nlinarith [mul_le_mul_of_nonneg_left hupper hc.le]

end SRWTightness
