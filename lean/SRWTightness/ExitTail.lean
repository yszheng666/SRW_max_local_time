import SRWTightness.ExitMoment

open MeasureTheory
open scoped ENNReal

namespace SRWTightness

 theorem prob_exitSteps_gt {R : ℝ} (hR : 0 ≤ R) (N : ℕ) (hN : 0 < N) :
    pathLaw.real {ω | N < exitSteps R ω} ≤ (R + 1) ^ 2 / N := by
  let f : Sample → ℝ := fun ω ↦ (exitSteps R ω : ℝ) / N
  have hf : Integrable f pathLaw := (integrable_exitSteps hR).div_const _
  have hn : 0 ≤ᵐ[pathLaw] f := Filter.Eventually.of_forall
    (fun ω ↦ div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hmeas := hf.measure_le_integral hn (s := {ω | N < exitSteps R ω}) (by
    intro ω hω
    apply (le_div_iff₀ (Nat.cast_pos.mpr hN)).mpr
    simpa only [one_mul] using (Nat.cast_le.mpr (Nat.le_of_lt hω) :
      (N : ℝ) ≤ exitSteps R ω))
  have hi : ∫ ω, f ω ∂pathLaw ≤ (R + 1) ^ 2 / N := by
    dsimp [f]
    rw [integral_div]
    exact div_le_div_of_nonneg_right (integral_exitSteps_le hR) (Nat.cast_nonneg _)
  have hb := hmeas.trans (ENNReal.ofReal_le_ofReal hi)
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  simpa only [measureReal_def, ENNReal.toReal_ofReal
    (div_nonneg (sq_nonneg (R + 1)) (Nat.cast_nonneg N))] using hr

 theorem prob_exit_gt {R : ℝ} (hR : 0 ≤ R) (N : ℕ) (hN : 0 < N) :
    pathLaw.real {ω | (N : WithTop ℕ) < exitTime R ω} ≤ (R + 1) ^ 2 / N := by
  have heq : {ω | (N : WithTop ℕ) < exitTime R ω} =ᵐ[pathLaw]
      {ω | N < exitSteps R ω} := by
    filter_upwards [exitTime_ne_top_ae hR] with ω hω
    apply propext
    change (N : WithTop ℕ) < exitTime R ω ↔ N < exitSteps R ω
    rw [← coe_exitSteps R ω hω]
    exact WithTop.coe_lt_coe
  rw [measureReal_congr heq]
  exact prob_exitSteps_gt hR N hN

end SRWTightness
