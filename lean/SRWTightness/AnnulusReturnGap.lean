import SRWTightness.AnnulusFineLogarithm
import SRWTightness.AnnulusEscapeIdentity

namespace SRWTightness

/-- At a full logarithmic scale above the target, the actual nonreturn probability has a log gap. -/
theorem annulus_return_gap (hinput : PotentialKernelAsymptoticInput) :
    ∃ a₀ : ℝ, 2 ≤ a₀ ∧ ∀ a R : ℝ, a₀ ≤ a → a < R → ∀ x : Site,
      Real.exp 1 * a ≤ Real.sqrt (normSq x) → normSq x ≤ R ^ 2 →
      1 / (2 * Real.log (R / a)) ≤ 1 - setHitProbability (diskFinset R) (diskFinset a) x := by
  obtain ⟨K, A, hK, hA, hh⟩ := annulus_log_formula hinput
  refine ⟨max A (2 * K), hA.trans (le_max_left _ _), ?_⟩
  intro a R ha hR x hx hxu
  have hAa : A ≤ a := (le_max_left _ _).trans ha
  have hKa : 2 * K ≤ a := (le_max_right _ _).trans ha
  have ha0 : 0 < a := by linarith
  have hR0 : 0 < R := ha0.trans hR
  have hexp : 1 ≤ Real.exp (1 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num)
  have hxa : a ≤ Real.sqrt (normSq x) := by nlinarith
  have hsq := Real.sq_sqrt (normSq_nonneg x)
  have hxl : a ^ 2 ≤ normSq x := by nlinarith [Real.sqrt_nonneg (normSq x)]
  obtain ⟨ε, he, hp⟩ := hh a R hAa hR x hxl hxu
  have hehalf : K / a ≤ 1 / 2 := (div_le_iff₀ ha0).mpr (by linarith)
  have helo : -(1 / 2 : ℝ) ≤ ε := by have hh := (abs_le.mp he).1; linarith
  have hratio : Real.exp 1 ≤ Real.sqrt (normSq x) / a := (le_div_iff₀ ha0).mpr hx
  have hnum : 1 ≤ Real.log (Real.sqrt (normSq x) / a) := by
    have ht := Real.log_le_log (Real.exp_pos 1) hratio
    simpa only [Real.log_exp] using ht
  have hden : 0 < Real.log (R / a) := Real.log_pos ((one_lt_div ha0).mpr hR)
  rw [← annulusOuterExitProbability_eq_one_sub_hit, hp]
  calc
    1 / (2 * Real.log (R / a)) = (1 / 2 : ℝ) / Real.log (R / a) := by ring
    _ ≤ (Real.log (Real.sqrt (normSq x) / a) + ε) / Real.log (R / a) :=
      div_le_div_of_nonneg_right (by linarith) hden.le

end SRWTightness
