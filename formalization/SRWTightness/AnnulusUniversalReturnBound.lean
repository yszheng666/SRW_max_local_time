import SRWTightness.AnnulusUniversalLogarithm
import SRWTightness.AnnulusEscapeIdentity

namespace SRWTightness

/-- A universal numerator error follows once the radius absorbs the asymptotic remainder. -/
theorem annulus_universal_return_bound (hinput : PotentialKernelAsymptoticInput) :
    ∃ A : ℝ, 2 ≤ A ∧ ∀ a R c : ℝ, A ≤ a → a < R → a ≤ c →
      ∀ x : Site, c ≤ Real.sqrt (normSq x) → normSq x ≤ R ^ 2 →
      setHitProbability (diskFinset R) (diskFinset a) x ≤
        1 - (Real.log (c / a) - 4 / a) / Real.log (R / a) := by
  obtain ⟨κ, C, R₀, hC, hR₀, hb⟩ := hinput
  have hg : 0 < (2 / Real.pi : ℝ) := by positivity
  refine ⟨max (R₀ + 1) (4 * C / (2 / Real.pi)),
    (by linarith : 2 ≤ R₀ + 1).trans (le_max_left _ _), ?_⟩
  intro a R c ha hR hac x hx hxu
  have ha₀ : R₀ + 1 ≤ a := (le_max_left _ _).trans ha
  have hCa : 4 * C ≤ (2 / Real.pi) * a := by
    have h := (div_le_iff₀ hg).mp ((le_max_right _ _).trans ha)
    nlinarith
  have ha0 : 0 < a := by linarith
  have hc0 : 0 < c := ha0.trans_le hac
  have hR0 : 0 < R := ha0.trans hR
  have hs := Real.sq_sqrt (normSq_nonneg x)
  have hxl : a ^ 2 ≤ normSq x := by nlinarith [Real.sqrt_nonneg (normSq x)]
  have hr0 : 0 < Real.sqrt (normSq x) := hc0.trans_le hx
  have he := annulus_log_numerator_universal κ C R₀ hC hR₀ hb
    a R (by linarith) ha₀ hR.le hCa x hxl hxu
  rw [← Real.log_div hR0.ne' ha0.ne', ← Real.log_div hr0.ne' ha0.ne'] at he
  have hn : Real.log (c / a) ≤ Real.log (Real.sqrt (normSq x) / a) :=
    Real.log_le_log (div_pos hc0 ha0) (div_le_div_of_nonneg_right hx ha0.le)
  have hd : 0 < Real.log (R / a) := Real.log_pos ((one_lt_div ha0).mpr hR)
  have hgap : (Real.log (c / a) - 4 / a) / Real.log (R / a) ≤
      annulusOuterExitProbability a R x := by
    apply (div_le_iff₀ hd).mpr
    linarith [(abs_le.mp he).1]
  rw [annulusOuterExitProbability_eq_one_sub_hit] at hgap
  linarith

end SRWTightness
