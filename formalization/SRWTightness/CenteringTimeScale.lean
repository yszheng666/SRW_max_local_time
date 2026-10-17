import SRWTightness.CenteringAlgebra
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Basic

open Filter
open scoped Topology

namespace SRWTightness

theorem diskCenter_sqrt_scale_difference (t c : ℝ) (ht : 1 < t) (hc : 0 < c)
    (hf : 0 < 1 + 2 * Real.log c / Real.log t) :
    diskCenter (c * Real.sqrt t) - (Real.log t - Real.log (Real.log t)) / Real.sqrt Real.pi =
      (Real.log 2 + 2 * Real.log c - Real.log (1 + 2 * Real.log c / Real.log t)) / Real.sqrt Real.pi := by
  have ht0 : 0 < t := by linarith
  have hl : 0 < Real.log t := Real.log_pos ht
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have he : Real.log c + Real.log t / 2 = (Real.log t / 2) * (1 + 2 * Real.log c / Real.log t) := by
    field_simp
    <;> ring
  have hlog : Real.log (Real.log (c * Real.sqrt t)) =
      Real.log (Real.log t) - Real.log 2 + Real.log (1 + 2 * Real.log c / Real.log t) := by
    rw [Real.log_mul hc.ne' hs.ne', Real.log_sqrt ht0.le, he,
      Real.log_mul (div_ne_zero hl.ne' (by norm_num)) hf.ne', Real.log_div hl.ne' (by norm_num)]
  unfold diskCenter
  rw [hlog, Real.log_mul hc.ne' hs.ne', Real.log_sqrt ht0.le]
  ring

theorem diskCenter_sqrt_scale_sub_timeCenter_tendsto (c : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ ↦ diskCenter (c * Real.sqrt n) - timeCenter n) atTop
      (𝓝 ((Real.log 2 + 2 * Real.log c) / Real.sqrt Real.pi)) := by
  have hlogNat : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun n : ℕ ↦ 2 * Real.log c / Real.log (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlogNat
  have hf : Tendsto (fun n : ℕ ↦ 1 + 2 * Real.log c / Real.log (n : ℝ)) atTop (𝓝 1) := by
    simpa using hsmall.const_add 1
  have hlog : Tendsto (fun n : ℕ ↦ Real.log (1 + 2 * Real.log c / Real.log (n : ℝ))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hf
  have hlim : Tendsto (fun n : ℕ ↦
      (Real.log 2 + 2 * Real.log c - Real.log (1 + 2 * Real.log c / Real.log (n : ℝ))) / Real.sqrt Real.pi)
      atTop (𝓝 ((Real.log 2 + 2 * Real.log c) / Real.sqrt Real.pi)) := by
    simpa using (tendsto_const_nhds.sub hlog).div_const (Real.sqrt Real.pi)
  apply hlim.congr'
  have ht : ∀ᶠ n : ℕ in atTop, 1 < (n : ℝ) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    exact_mod_cast (show 1 < n by omega)
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < 1 + 2 * Real.log c / Real.log (n : ℝ) :=
    hf.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [ht, hpos] with n htn hfn
  exact (diskCenter_sqrt_scale_difference (n : ℝ) c htn hc hfn).symm

end SRWTightness
