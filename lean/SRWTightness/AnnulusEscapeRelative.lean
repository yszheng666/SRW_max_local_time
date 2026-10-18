import SRWTightness.AnnulusFineLogarithm
import SRWTightness.AnnulusEscapeEvent
import SRWTightness.LogRadiusOvershoot

namespace SRWTightness

/-- The actual long-annulus escape law has uniform relative error at every short-exit overshoot. -/
theorem annulus_escape_relative (hP : PotentialKernelAsymptoticInput) :
    ∃ C a₀ : ℝ, 0 < C ∧ 2 ≤ a₀ ∧ ∀ a b R : ℝ,
      a₀ ≤ a → 2 * a ≤ b → b + 1 ≤ R → ∀ c x : Site,
      b ≤ Real.sqrt (normSq (x - c)) → Real.sqrt (normSq (x - c)) ≤ b + 1 →
      ∃ δ : ℝ, |δ| ≤ C / a ∧
        pathLaw.real {ω | domainExit (translateFinset c (diskFinset R)) x ω <
          setHittingTime (translateFinset c (diskFinset a)) x 0 ω} =
          (Real.log (b / a) / Real.log (R / a)) * (1 + δ) := by
  obtain ⟨G, a₀, hG, ha₀, hh⟩ := annulus_log_formula hP
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(G + 2) / Real.log 2, a₀, by positivity, ha₀, ?_⟩
  intro a b R ha hb hR c x hxl hxu
  have ha2 : 2 ≤ a := ha₀.trans ha
  have ha0 : 0 < a := by linarith
  have hb2 : 2 ≤ b := by linarith
  have hb0 : 0 < b := by linarith
  have hab : a ≤ b := by linarith
  have haR : a < R := by linarith
  have hR0 : 0 < R := by linarith
  have hs := Real.sq_sqrt (normSq_nonneg (x - c))
  have hrl : a ^ 2 ≤ normSq (x - c) := by nlinarith [Real.sqrt_nonneg (normSq (x - c))]
  have hru : normSq (x - c) ≤ R ^ 2 := by nlinarith [Real.sqrt_nonneg (normSq (x - c))]
  obtain ⟨ε, hε, hp⟩ := hh a R ha haR (x - c) hrl hru
  have hr0 : 0 < Real.sqrt (normSq (x - c)) := by linarith
  have hunit := log_radius_unit_error (Real.sqrt (normSq (x - c))) b hb2 (by linarith) hxu
  have hlogs : |Real.log (Real.sqrt (normSq (x - c)) / a) - Real.log (b / a)| ≤ 2 / b := by
    rw [Real.log_div hr0.ne' ha0.ne', Real.log_div hb0.ne' ha0.ne']
    simpa only [sub_sub_sub_cancel_right] using hunit
  have hL : Real.log 2 ≤ Real.log (b / a) :=
    Real.log_le_log (by norm_num) ((le_div_iff₀ ha0).mpr hb)
  have hL0 : 0 < Real.log (b / a) := hlog2.trans_le hL
  have hT0 : 0 < Real.log (R / a) := Real.log_pos ((one_lt_div ha0).mpr haR)
  let δ := (Real.log (Real.sqrt (normSq (x - c)) / a) - Real.log (b / a) + ε) /
    Real.log (b / a)
  refine ⟨δ, ?_, ?_⟩
  · have hnum : |Real.log (Real.sqrt (normSq (x - c)) / a) - Real.log (b / a) + ε| ≤
        (G + 2) / a := by
      calc
        _ ≤ |Real.log (Real.sqrt (normSq (x - c)) / a) - Real.log (b / a)| + |ε| := abs_add_le _ _
        _ ≤ 2 / b + G / a := add_le_add hlogs hε
        _ ≤ 2 / a + G / a := add_le_add (div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 2 by norm_num) ha0 hab) (le_refl (G / a))
        _ = (G + 2) / a := by ring
    dsimp only [δ]
    rw [abs_div, abs_of_pos hL0]
    calc
      _ ≤ ((G + 2) / a) / Real.log (b / a) := div_le_div_of_nonneg_right hnum hL0.le
      _ ≤ ((G + 2) / a) / Real.log 2 :=
        div_le_div_of_nonneg_left (by positivity) hlog2 hL
      _ = ((G + 2) / Real.log 2) / a := by ring
  · rw [translated_annulus_escape_probability a R ha0.le haR.le c x, hp]
    dsimp only [δ]
    field_simp
    <;> ring

end SRWTightness
