import SRWTightness.CenteringAlgebra
import Mathlib.Analysis.SpecificLimits.Basic

open Filter
open scoped Topology

namespace SRWTightness

theorem logLog_nat_increment_tendsto_zero :
    Tendsto (fun n : ℕ ↦ Real.log (Real.log (n + 1 : ℕ)) - Real.log (Real.log (n : ℝ))) atTop (𝓝 0) := by
  have hlogNat : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hdelta : Tendsto (fun n : ℕ ↦ Real.log (n + 1 : ℕ) - Real.log (n : ℝ)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using Real.tendsto_log_nat_add_one_sub_log
  have hinv : Tendsto (fun n : ℕ ↦ 1 / Real.log (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlogNat
  have hsmall : Tendsto (fun n : ℕ ↦ (Real.log (n + 1 : ℕ) - Real.log (n : ℝ)) / Real.log (n : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_one_div, mul_zero] using hdelta.mul hinv
  have hr : Tendsto (fun n : ℕ ↦ 1 + (Real.log (n + 1 : ℕ) - Real.log (n : ℝ)) / Real.log (n : ℝ)) atTop (𝓝 1) := by
    simpa using hsmall.const_add 1
  have hl : Tendsto (fun n : ℕ ↦ Real.log (1 + (Real.log (n + 1 : ℕ) - Real.log (n : ℝ)) / Real.log (n : ℝ))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hr
  apply hl.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hnp1 : (1 : ℝ) < (n + 1 : ℕ) := by exact_mod_cast (show 1 < n + 1 by omega)
  have hln := Real.log_pos hn1
  have hlnp := Real.log_pos hnp1
  have he : 1 + (Real.log (n + 1 : ℕ) - Real.log (n : ℝ)) / Real.log (n : ℝ) =
      Real.log (n + 1 : ℕ) / Real.log (n : ℝ) := by field_simp <;> ring
  rw [he, Real.log_div hlnp.ne' hln.ne']

theorem timeCenter_increment_tendsto_zero :
    Tendsto (fun n : ℕ ↦ timeCenter (n + 1) - timeCenter n) atTop (𝓝 0) := by
  have hd : Tendsto (fun n : ℕ ↦ Real.log (n + 1 : ℕ) - Real.log (n : ℝ)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using Real.tendsto_log_nat_add_one_sub_log
  have h := (hd.sub logLog_nat_increment_tendsto_zero).div_const (Real.sqrt Real.pi)
  convert h using 1
  · ext n
    unfold timeCenter
    ring
  · simp

end SRWTightness
