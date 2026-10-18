import SRWTightness.ExternalExponentialFloorScale
import Mathlib.Analysis.Complex.ExponentialBounds

namespace SRWTightness

/-- All rounded-exponential scale conditions follow from elementary real inequalities. -/
theorem exponential_floor_scale_input : ExponentialFloorScaleInput := by
  intro c hc
  let L : ℝ := max 1 (max (Real.log (64 * c)) (Real.log (2 / c)))
  refine ⟨4 * L, by dsimp [L]; positivity, ?_⟩
  intro u hu
  have hL : 1 ≤ L := le_max_left _ _
  have hu4 : L ≤ u / 4 := by linarith
  have hu0 : 0 ≤ u := by linarith
  have ha : 1 ≤ u / 4 := hL.trans hu4
  have ha64 : Real.log (64 * c) ≤ u / 4 :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hu4)
  have ha2 : Real.log (2 / c) ≤ u / 4 :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hu4)
  have hexp2 : 2 ≤ Real.exp (u / 4) :=
    Real.exp_one_gt_two.le.trans (Real.exp_le_exp.mpr ha)
  have hc2 : 2 ≤ c * Real.exp (u / 4) := by
    have hh := Real.exp_le_exp.mpr ha2
    rw [Real.exp_log (div_pos (by norm_num) hc)] at hh
    have hh' := (div_le_iff₀ hc).mp hh
    nlinarith
  have hrle : upperTerminalFineRadius u ≤ Real.exp (u / 4) :=
    Nat.floor_le (Real.exp_pos _).le
  have hrlt : Real.exp (u / 4) < upperTerminalFineRadius u + 1 :=
    Nat.lt_floor_add_one _
  have hrhalf : Real.exp (u / 4) / 2 ≤ upperTerminalFineRadius u := by linarith
  have hr1 : 1 ≤ upperTerminalFineRadius u := by linarith
  have hcr : 1 ≤ c * upperTerminalFineRadius u := by
    nlinarith [mul_le_mul_of_nonneg_left hrhalf hc.le]
  have he1 : 1 ≤ Real.exp u := Real.one_le_exp_iff.mpr hu0
  have hRlo : Real.exp u ≤ upperTerminalRadius u := by
    unfold upperTerminalRadius
    rw [Real.exp_add]
    nlinarith [Real.exp_one_gt_two]
  have hRhi : upperTerminalRadius u ≤ Real.exp (u + 1) := by
    unfold upperTerminalRadius
    linarith
  have hR2 : 2 ≤ upperTerminalRadius u := by
    have hh : Real.exp (u / 4) ≤ Real.exp u :=
      Real.exp_le_exp.mpr (by linarith)
    exact hexp2.trans (hh.trans hRlo)
  have hc64 : 64 * c ≤ Real.exp (3 * u / 4) := by
    have hh := Real.exp_le_exp.mpr
      (show Real.log (64 * c) ≤ 3 * u / 4 by linarith)
    rwa [Real.exp_log (mul_pos (by norm_num) hc)] at hh
  have hscale : 64 * (c * upperTerminalFineRadius u) ≤ upperTerminalRadius u := by
    have hh := mul_le_mul_of_nonneg_right hc64 (Real.exp_pos (u / 4)).le
    have he : Real.exp (3 * u / 4) * Real.exp (u / 4) = Real.exp u := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he] at hh
    have hh' := mul_le_mul_of_nonneg_left hrle (show 0 ≤ 64 * c by positivity)
    nlinarith
  have hlogRlo : u ≤ Real.log (upperTerminalRadius u) := by
    have hh := Real.log_le_log (Real.exp_pos u) hRlo
    simpa only [Real.log_exp] using hh
  have hlogRhi : Real.log (upperTerminalRadius u) ≤ u + 1 := by
    have hh := Real.log_le_log (by linarith : 0 < upperTerminalRadius u) hRhi
    simpa only [Real.log_exp] using hh
  have hlogrhi : Real.log (upperTerminalFineRadius u) ≤ u / 4 := by
    have hh := Real.log_le_log (by linarith : 0 < upperTerminalFineRadius u) hrle
    simpa only [Real.log_exp] using hh
  have hlogrlo : u / 4 - 1 ≤ Real.log (upperTerminalFineRadius u) := by
    have hh := Real.log_le_log (div_pos (Real.exp_pos _) (by norm_num)) hrhalf
    rw [Real.log_div (Real.exp_ne_zero _) (by norm_num), Real.log_exp] at hh
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  refine ⟨hR2, hr1, hcr, hscale, ?_, ?_⟩
  · exact abs_le.mpr ⟨by linarith, by linarith⟩
  · exact abs_le.mpr ⟨by linarith, by linarith⟩

end SRWTightness
