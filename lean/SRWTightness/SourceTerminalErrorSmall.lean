import SRWTightness.SourceCapacityHalfProfile
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace SRWTightness

/-- The source cutoff gives a uniform small terminal relative error from a scalar time threshold. -/
theorem source_terminal_error_small (W m a t : ℝ) (hW : 0 ≤ W) (ht : 2 ≤ t)
    (hWt : 8 * W ≤ t) (ha : 1 ≤ a) (hcut : a ≤ m / t ^ 6) :
    W * (a + 1) / m * Real.log (m / a) ≤ 1 / 2 := by
  have ht0 : 0 < t := by linarith
  have ha0 : 0 < a := by linarith
  have hmul := (le_div_iff₀ (pow_pos ht0 6)).mp hcut
  have hm0 : 0 < m := (mul_pos ha0 (pow_pos ht0 6)).trans_le hmul
  let s := Real.sqrt (m / a)
  have hs : 0 < s := Real.sqrt_pos.2 (div_pos hm0 ha0)
  have hsq : s ^ 2 = m / a := Real.sq_sqrt (div_nonneg hm0.le ha0.le)
  have hmform : s ^ 2 * a = m := (eq_div_iff ha0.ne').mp hsq
  have hr : t ^ 6 ≤ m / a := (le_div_iff₀ ha0).mpr (by nlinarith [hmul])
  have ht26 : t ^ 2 ≤ t ^ 6 := pow_le_pow_right₀ (by linarith : 1 ≤ t) (by norm_num)
  have hts : t ≤ s := by nlinarith [ht26.trans hr]
  have hl : Real.log (m / a) ≤ 2 * s := by
    have hh := Real.log_le_rpow_div (div_nonneg hm0.le ha0.le)
      (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at hh
    dsimp [s]
    linarith
  calc
    W * (a + 1) / m * Real.log (m / a) ≤ W * (a + 1) / m * (2 * s) :=
      mul_le_mul_of_nonneg_left hl (by positivity)
    _ ≤ 1 / 2 := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hm0).mpr
      have h1 := mul_le_mul_of_nonneg_left (show a + 1 ≤ 2 * a by linarith)
        (mul_nonneg hW hs.le)
      have h2 := mul_le_mul_of_nonneg_left (hWt.trans hts) (mul_nonneg ha0.le hs.le)
      nlinarith

/-- Both formerly explicit terminal smallness premises hold for the actual source profile. -/
theorem source_terminal_smallness_profile (b : Site) (t a W : ℝ) (K : Finset Site)
    (hW : 0 ≤ W) (ht : max sourceCapacityHalfThreshold (8 * W) ≤ t) (ha : 1 ≤ a)
    (hcut : a ≤ sourceLowerRadius t / t ^ 6) (hK : K ⊆ translateFinset b (diskFinset a)) :
    sourceReferenceIntensity (sourceLowerRadius t) 14 *
        capacity (translateFinset b (diskFinset (Real.exp 1 * sourceLowerRadius t + 14))) K ≤ 1 / 2 ∧
      W * (a + 1) / sourceLowerRadius t * Real.log (sourceLowerRadius t / a) ≤ 1 / 2 := by
  have htcap : sourceCapacityHalfThreshold ≤ t := (le_max_left _ _).trans ht
  have htbase : sourceScaleThreshold 4 ≤ t := (le_max_left _ _).trans htcap
  exact ⟨source_capacity_half_profile b t a K htcap ha hcut hK,
    source_terminal_error_small W _ a t hW
      (sourceScaleThreshold_conditions t 4 (by norm_num) htbase).1
      ((le_max_right _ _).trans ht) ha hcut⟩

end SRWTightness
