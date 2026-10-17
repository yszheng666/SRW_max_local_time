import SRWTightness.SourceUpperDepthInternal

open Filter
open scoped Topology
namespace SRWTightness

/-- The exact logarithmic mesh suppresses the polynomial error in source (4.3). -/
theorem source_upper_mesh_exponential_internal :
    Tendsto (fun t : ℝ ↦ t ^ 2 * sourceUpperLogRadius t *
      Real.exp (-3 * sourceUpperLogRadius t / 4)) atTop (𝓝 0) := by
  have hi : Tendsto (fun t : ℝ ↦ 4 / t) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ ↦ t⁻¹) atTop (𝓝 0)).const_mul 4
  apply squeeze_zero' ?_ ?_ hi
  · exact Filter.Eventually.of_forall (fun t ↦ by unfold sourceUpperLogRadius; positivity)
  · filter_upwards [eventually_ge_atTop (Real.exp 1)] with t ht
    have ht0 : 0 < t := (Real.exp_pos _).trans_le ht
    have hl : 1 ≤ Real.log t := by
      have hh := Real.log_le_log (Real.exp_pos 1) ht
      simpa only [Real.log_exp] using hh
    have hp : Real.log t ≤ (Real.log t) ^ 4 := by
      nlinarith [sq_nonneg (Real.log t - 1), sq_nonneg ((Real.log t) ^ 2 - 1)]
    have hD : 3 * Real.log t ≤ sourceUpperLogRadius t / 2 := by
      unfold sourceUpperLogRadius
      nlinarith
    have hpow : t ^ 3 ≤ Real.exp (sourceUpperLogRadius t / 2) := by
      have hh := Real.exp_le_exp.mpr hD
      have he : Real.exp (3 * Real.log t) = t ^ 3 := by
        rw [show 3 * Real.log t = Real.log t + Real.log t + Real.log t by ring,
          Real.exp_add, Real.exp_add, Real.exp_log ht0]
        ring
      rwa [he] at hh
    have hratio : t ^ 2 * Real.exp (-sourceUpperLogRadius t / 2) ≤ 1 / t := by
      rw [show -sourceUpperLogRadius t / 2 = -(sourceUpperLogRadius t / 2) by ring,
        Real.exp_neg, ← div_eq_mul_inv]
      apply (div_le_div_iff₀ (Real.exp_pos _) ht0).mpr
      nlinarith
    have hlin : sourceUpperLogRadius t ≤ 4 * Real.exp (sourceUpperLogRadius t / 4) := by
      have hh := Real.add_one_le_exp (sourceUpperLogRadius t / 4)
      linarith
    have hh := mul_le_mul_of_nonneg_right hlin
      (Real.exp_pos (-3 * sourceUpperLogRadius t / 4)).le
    have he : Real.exp (sourceUpperLogRadius t / 4) *
        Real.exp (-3 * sourceUpperLogRadius t / 4) =
        Real.exp (-sourceUpperLogRadius t / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hh' : sourceUpperLogRadius t * Real.exp (-3 * sourceUpperLogRadius t / 4) ≤
        4 * Real.exp (-sourceUpperLogRadius t / 2) := by nlinarith [he]
    calc
      t ^ 2 * sourceUpperLogRadius t * Real.exp (-3 * sourceUpperLogRadius t / 4) =
          t ^ 2 * (sourceUpperLogRadius t *
            Real.exp (-3 * sourceUpperLogRadius t / 4)) := by ring
      _ ≤ t ^ 2 * (4 * Real.exp (-sourceUpperLogRadius t / 2)) :=
        mul_le_mul_of_nonneg_left hh' (sq_nonneg t)
      _ = 4 * (t ^ 2 * Real.exp (-sourceUpperLogRadius t / 2)) := by ring
      _ ≤ 4 * (1 / t) := mul_le_mul_of_nonneg_left hratio (by norm_num)
      _ = 4 / t := by ring

end SRWTightness
