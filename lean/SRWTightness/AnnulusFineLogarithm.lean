import SRWTightness.AnnulusFinePayoff

namespace SRWTightness

/-- The logarithmic numerator error is uniform in the outer radius and starting point. -/
theorem annulus_log_numerator_error (κ C R₀ : ℝ) (hC : 0 ≤ C) (hR₀ : 1 ≤ R₀)
    (hbound : ∀ z : Site, R₀ ≤ Real.sqrt (normSq z) →
      |potentialKernel z - ((2 / Real.pi) * Real.log (Real.sqrt (normSq z)) + κ)| ≤ C / normSq z)
    (a R : ℝ) (ha : 2 ≤ a) (ha₀ : R₀ + 1 ≤ a) (haR : a ≤ R)
    (x : Site) (hxl : a ^ 2 ≤ normSq x) (hxu : normSq x ≤ R ^ 2) :
    |annulusOuterExitProbability a R x * (Real.log R - Real.log a) -
      (Real.log (Real.sqrt (normSq x)) - Real.log a)| ≤
      ((5 * C + 2 * (2 / Real.pi)) / a) / (2 / Real.pi) := by
  have ha0 : 0 < a := by linarith
  have hx0 : 0 < normSq x := by nlinarith
  have hroot : a ≤ Real.sqrt (normSq x) :=
    (Real.le_sqrt ha0.le (normSq_nonneg x)).mpr hxl
  have hp := hbound x (by linarith)
  have hdiv : C / normSq x ≤ C / a := by
    exact div_le_div_of_nonneg_left hC ha0 (by nlinarith)
  have hp' := hp.trans hdiv
  have he := annulus_potential_exit_approximation κ C R₀ hC hR₀ hbound
    a R ha ha₀ haR x hxl hxu
  have hg : 0 < (2 / Real.pi : ℝ) := by positivity
  apply (le_div_iff₀ hg).mpr
  conv_lhs => rw [← abs_of_pos hg, ← abs_mul]
  apply abs_le.mpr
  have hpL := (abs_le.mp hp').1
  have hpU := (abs_le.mp hp').2
  have heL := (abs_le.mp he).1
  have heU := (abs_le.mp he).2
  have hs : C / a + (4 * C + 2 * (2 / Real.pi)) / a =
      (5 * C + 2 * (2 / Real.pi)) / a := by ring
  constructor <;> nlinarith [hs]

/-- A uniform fine annulus formula conditional only on the standard potential asymptotics. -/
theorem annulus_log_formula (hinput : PotentialKernelAsymptoticInput) :
    ∃ K a₀ : ℝ, 0 ≤ K ∧ 2 ≤ a₀ ∧ ∀ a R : ℝ, a₀ ≤ a → a < R →
      ∀ x : Site, a ^ 2 ≤ normSq x → normSq x ≤ R ^ 2 →
        ∃ ε : ℝ, |ε| ≤ K / a ∧
          annulusOuterExitProbability a R x =
            (Real.log (Real.sqrt (normSq x) / a) + ε) / Real.log (R / a) := by
  obtain ⟨κ, C, R₀, hC, hR₀, hb⟩ := hinput
  refine ⟨(5 * C + 2 * (2 / Real.pi)) / (2 / Real.pi), R₀ + 1,
    by positivity, by linarith, ?_⟩
  intro a R ha hR x hxl hxu
  have ha0 : 0 < a := by linarith
  have hR0 : 0 < R := by linarith
  have hx0 : 0 < normSq x := by nlinarith
  have hr0 : 0 < Real.sqrt (normSq x) := Real.sqrt_pos.mpr hx0
  have hlog : 0 < Real.log R - Real.log a := by
    have hh := Real.strictMonoOn_log ha0 hR0 hR
    linarith
  let ε := annulusOuterExitProbability a R x * (Real.log R - Real.log a) -
    (Real.log (Real.sqrt (normSq x)) - Real.log a)
  refine ⟨ε, ?_, ?_⟩
  · have he := annulus_log_numerator_error κ C R₀ hC hR₀ hb a R
      (by linarith) ha hR.le x hxl hxu
    convert he using 1 <;> ring
  · rw [Real.log_div hr0.ne' ha0.ne', Real.log_div hR0.ne' ha0.ne']
    apply (eq_div_iff hlog.ne').mpr
    dsimp only [ε]
    ring

end SRWTightness
