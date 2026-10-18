import SRWTightness.AnnulusFineLogarithm
import SRWTightness.AnnulusEscapeIdentity

namespace SRWTightness

/-- The fine return bound retains its numerator error instead of losing a fixed factor. -/
theorem annulus_fine_return_bound (hinput : PotentialKernelAsymptoticInput) :
    ∃ K a₀ : ℝ, 0 ≤ K ∧ 2 ≤ a₀ ∧ ∀ a R c : ℝ, a₀ ≤ a → a < R → a ≤ c →
      ∀ x : Site, c ≤ Real.sqrt (normSq x) → normSq x ≤ R ^ 2 →
      setHitProbability (diskFinset R) (diskFinset a) x ≤
        1 - (Real.log (c / a) - K / a) / Real.log (R / a) := by
  obtain ⟨K, a₀, hK, ha₀, hh⟩ := annulus_log_formula hinput
  refine ⟨K, a₀, hK, ha₀, ?_⟩
  intro a R c ha hR hac x hx hxu
  have ha0 : 0 < a := by linarith
  have hc0 : 0 < c := ha0.trans_le hac
  have hsq := Real.sq_sqrt (normSq_nonneg x)
  have hxl : a ^ 2 ≤ normSq x := by nlinarith [Real.sqrt_nonneg (normSq x)]
  obtain ⟨ε, he, hp⟩ := hh a R ha hR x hxl hxu
  have hnum : Real.log (c / a) ≤ Real.log (Real.sqrt (normSq x) / a) :=
    Real.log_le_log (div_pos hc0 ha0) (div_le_div_of_nonneg_right hx ha0.le)
  have helo := (abs_le.mp he).1
  have hden : 0 < Real.log (R / a) := Real.log_pos ((one_lt_div ha0).mpr hR)
  have hgap : (Real.log (c / a) - K / a) / Real.log (R / a) ≤
      annulusOuterExitProbability a R x := by
    rw [hp]
    exact div_le_div_of_nonneg_right (by linarith) hden.le
  rw [annulusOuterExitProbability_eq_one_sub_hit] at hgap
  linarith

end SRWTightness
