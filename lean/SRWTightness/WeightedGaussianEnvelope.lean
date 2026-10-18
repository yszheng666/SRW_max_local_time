import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory Filter Set
namespace SRWTightness

/-- A Gaussian linear weight is absorbed by a half-strength Gaussian with the exact scale factor. -/
theorem weighted_gaussian_half_exponent (k z : ℝ) (hk : 0 < k) :
    (1 + z) * Real.exp (-k * z ^ 2) ≤
      (1 + 1 / Real.sqrt k) * Real.exp (-(k / 2) * z ^ 2) := by
  have hs : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk
  have hu : Real.sqrt k * z ≤ Real.exp (k * z ^ 2 / 2) := by
    have hb : Real.sqrt k * z ≤ 1 + (Real.sqrt k * z) ^ 2 / 2 := by
      nlinarith [sq_nonneg (Real.sqrt k * z - 1)]
    have he : (Real.sqrt k * z) ^ 2 = k * z ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hk.le]
    rw [he] at hb
    exact hb.trans (by linarith [Real.add_one_le_exp (k * z ^ 2 / 2)])
  have hm := mul_le_mul_of_nonneg_right hu (Real.exp_nonneg (-(k * z ^ 2 / 2)))
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hm
  have hz : z * Real.exp (-(k * z ^ 2 / 2)) ≤ 1 / Real.sqrt k := by
    rw [le_div_iff₀ hs]
    nlinarith
  have he : Real.exp (-(k * z ^ 2 / 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (div_nonneg (mul_nonneg hk.le (sq_nonneg z))
      (by norm_num)))
  have hf : Real.exp (-k * z ^ 2) =
      Real.exp (-(k * z ^ 2 / 2)) * Real.exp (-(k * z ^ 2 / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (Real.exp (-(k * z ^ 2 / 2)) + z * Real.exp (-(k * z ^ 2 / 2))) *
        Real.exp (-(k * z ^ 2 / 2)) := by rw [hf]; ring
    _ ≤ (1 + 1 / Real.sqrt k) * Real.exp (-(k * z ^ 2 / 2)) :=
      mul_le_mul_of_nonneg_right (add_le_add he hz) (Real.exp_nonneg _)
    _ = _ := by congr 1; congr 1; ring

/-- Every closed interval weighted Gaussian integral is bounded by an explicit full-line integral.
-/
theorem weighted_gaussian_interval_bound (k a : ℝ) (hk : 0 < k) :
    (∫ z in Icc 0 a, (1 + z) * Real.exp (-k * z ^ 2)) ≤
      (1 + 1 / Real.sqrt k) * Real.sqrt (Real.pi / (k / 2)) := by
  have hg : Integrable (fun z : ℝ ↦
      (1 + 1 / Real.sqrt k) * Real.exp (-(k / 2) * z ^ 2)) volume :=
    (integrable_exp_neg_mul_sq (by positivity : 0 < k / 2)).const_mul _
  have hi := setIntegral_mono_on (s := Icc 0 a)
    (show Continuous (fun z : ℝ ↦ (1 + z) * Real.exp (-k * z ^ 2)) by
      fun_prop).continuousOn.integrableOn_Icc hg.integrableOn measurableSet_Icc
    (fun z _ ↦ weighted_gaussian_half_exponent k z hk)
  have hnonneg : ∀ᵐ z : ℝ ∂volume,
      0 ≤ (1 + 1 / Real.sqrt k) * Real.exp (-(k / 2) * z ^ 2) :=
    Eventually.of_forall (fun z : ℝ ↦ by positivity)
  have hwhole := setIntegral_le_integral (s := Icc 0 a) hg hnonneg
  have hb := hi.trans hwhole
  rw [integral_const_mul, integral_gaussian (k / 2)] at hb
  exact hb

end SRWTightness
