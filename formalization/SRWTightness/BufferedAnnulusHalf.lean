import SRWTightness.AnnulusHalfComparison
import SRWTightness.BufferedAnnulusGeometry

namespace SRWTightness

/-- Uniform half-probability control for the buffered geometric annuli used by source records. -/
theorem buffered_annulus_half (hinput : PotentialKernelAsymptoticInput) :
    ∃ K T : ℝ, 0 ≤ K ∧ 2 ≤ T ∧ ∀ ρ H : ℝ, 1 ≤ H → 8 * H ≤ ρ → T ≤ ρ - H →
      ∀ x : Site, |Real.sqrt (normSq x) - Real.exp 1 * ρ| ≤ 2 * H →
        |annulusOuterExitProbability (ρ - H) (Real.exp 2 * ρ + H) x - 1 / 2| ≤ K * H / ρ := by
  obtain ⟨κ, C, R₀, hC, hR₀, hb⟩ := hinput
  let A := (5 * C + 2 * (2 / Real.pi)) / (2 / Real.pi)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨2 * A + 8, R₀ + 1, by positivity, by linarith, ?_⟩
  intro ρ H hH hρ hT x hx
  have hρ0 : 0 < ρ := by linarith
  have ha0 : 0 < ρ - H := by linarith
  obtain ⟨ha, haR, hxl, hxu⟩ := buffered_middle_annulus_geometry ρ H hH hρ x hx
  have hla : |Real.log (ρ - H) - Real.log ρ| ≤ 4 * H / ρ := by
    have hh := geometric_radius_log_error (ρ - H) ρ H 0 (by linarith) (by linarith)
      (by norm_num) (by simp only [Real.exp_zero, one_mul]; apply abs_le.mpr; constructor <;> linarith)
    simpa only [add_zero] using hh
  have hlx := geometric_radius_log_error (Real.sqrt (normSq x)) ρ H 1
    (by linarith) (by linarith) (by norm_num) hx
  have hlR := geometric_radius_log_error (Real.exp 2 * ρ + H) ρ H 2
    (by linarith) (by linarith) (by norm_num)
    (by apply abs_le.mpr; constructor <;> linarith)
  have hh := annulus_half_of_log_radius_bounds κ C R₀ hC hR₀ hb
    (ρ - H) (Real.exp 2 * ρ + H) ha hT haR x hxl hxu (Real.log ρ) (4 * H / ρ)
    (by apply (div_le_iff₀ hρ0).mpr; linarith) hla hlx hlR
  have he : ((5 * C + 2 * (2 / Real.pi)) / (ρ - H)) / (2 / Real.pi) =
      A / (ρ - H) := by dsimp [A]; ring
  rw [he] at hh
  have hdiv : A / (ρ - H) ≤ (2 * A) / ρ := by
    apply (div_le_div_iff₀ ha0 hρ0).mpr
    nlinarith [mul_nonneg hA (show 0 ≤ ρ - 2 * H by linarith)]
  apply hh.trans
  calc
    A / (ρ - H) + 2 * (4 * H / ρ) ≤ (2 * A) / ρ + 2 * (4 * H / ρ) :=
      add_le_add hdiv le_rfl
    _ ≤ (2 * A + 8) * H / ρ := by
      apply (le_div_iff₀ hρ0).mpr
      have heq : ((2 * A) / ρ + 2 * (4 * H / ρ)) * ρ = 2 * A + 8 * H := by field_simp <;> ring
      rw [heq]
      nlinarith [mul_nonneg hA (sub_nonneg.mpr hH)]

end SRWTightness
