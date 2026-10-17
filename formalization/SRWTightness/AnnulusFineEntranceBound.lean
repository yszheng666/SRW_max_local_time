import SRWTightness.AnnulusFineReturnBound

namespace SRWTightness

/-- A fine first-entrance lower bound with the original potential-kernel error retained. -/
theorem annulus_fine_entrance_bound (hinput : PotentialKernelAsymptoticInput) :
    ∃ K A : ℝ, 0 ≤ K ∧ 2 ≤ A ∧ ∀ a R c : ℝ,
      A ≤ a → a ≤ c → c < R → ∀ x : Site,
      a ≤ Real.sqrt (normSq x) → Real.sqrt (normSq x) ≤ c →
      (Real.log (R / c) - K / a) / Real.log (R / a) ≤
        setHitProbability (diskFinset R) (diskFinset a) x := by
  obtain ⟨K, A, hK, hA, hh⟩ := annulus_log_formula hinput
  refine ⟨K, A, hK, hA, ?_⟩
  intro a R c ha hac hcR x hxa hxc
  have ha0 : 0 < a := by linarith
  have hc0 : 0 < c := by linarith
  have hR0 : 0 < R := by linarith
  have hsq := Real.sq_sqrt (normSq_nonneg x)
  have hx0 := Real.sqrt_nonneg (normSq x)
  obtain ⟨ε, he, hp⟩ := hh a R ha (by linarith) x (by nlinarith) (by nlinarith)
  have hden : 0 < Real.log (R / a) := Real.log_pos ((one_lt_div ha0).mpr (by linarith))
  have hnum : Real.log (Real.sqrt (normSq x) / a) ≤ Real.log (c / a) :=
    Real.log_le_log (div_pos (by linarith) ha0)
      (div_le_div_of_nonneg_right hxc ha0.le)
  have hup : annulusOuterExitProbability a R x ≤
      (Real.log (c / a) + K / a) / Real.log (R / a) := by
    rw [hp]
    exact div_le_div_of_nonneg_right (by linarith [(abs_le.mp he).2]) hden.le
  rw [annulusOuterExitProbability_eq_one_sub_hit] at hup
  have hlog : Real.log (R / c) = Real.log (R / a) - Real.log (c / a) := by
    rw [Real.log_div hR0.ne' hc0.ne', Real.log_div hR0.ne' ha0.ne',
      Real.log_div hc0.ne' ha0.ne']
    ring
  have hf : (Real.log (R / c) - K / a) / Real.log (R / a) =
      1 - (Real.log (c / a) + K / a) / Real.log (R / a) := by
    rw [hlog]
    field_simp
    <;> ring
  rw [hf]
  linarith

end SRWTightness
