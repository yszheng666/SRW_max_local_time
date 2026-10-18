import SRWTightness.UpperGeometricRootGaussian
import Mathlib.Analysis.SumIntegralComparisons

open Set MeasureTheory

namespace SRWTightness

/-- A unit interval comparison broadens the centered Gaussian without changing its leading cost. -/
theorem upper_root_gaussian_window (q c : ℝ) (J : ℕ) (x : ℝ)
    (hq : 1 ≤ q) (hx : x ∈ Ico (J : ℝ) (J + 1)) :
    (J : ℝ) ^ (1 / 4 : ℝ) *
        Real.exp (-((Real.sqrt (2 * (J : ℝ)) - c) ^ 2 / (2 * q))) ≤
      Real.exp 1 * (x ^ (1 / 4 : ℝ) *
        Real.exp (-((Real.sqrt (2 * x) - c) ^ 2 / (4 * q)))) := by
  have hq0 : 0 < q := by linarith
  have hx0 : 0 ≤ x := (Nat.cast_nonneg J).trans hx.1
  let A := Real.sqrt (2 * (J : ℝ))
  let B := Real.sqrt (2 * x)
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hBA : A ≤ B := Real.sqrt_le_sqrt (by linarith [hx.1])
  have hAsq : A ^ 2 = 2 * (J : ℝ) := Real.sq_sqrt (by positivity)
  have hBsq : B ^ 2 = 2 * x := Real.sq_sqrt (by positivity)
  have hdiff : (B - A) ^ 2 ≤ 2 := by nlinarith [hx.2]
  have hsq : (B - c) ^ 2 ≤ 2 * (A - c) ^ 2 + 4 := by
    nlinarith [sq_nonneg ((A - c) - (B - A))]
  have hdiv := div_le_div_of_nonneg_right hsq (by positivity : 0 ≤ 4 * q)
  have hid : (2 * (A - c) ^ 2 + 4) / (4 * q) = (A - c) ^ 2 / (2 * q) + 1 / q := by
    field_simp [hq0.ne']
    ring
  rw [hid] at hdiv
  have hinv : 1 / q ≤ 1 := (div_le_one hq0).mpr hq
  have he : -((A - c) ^ 2 / (2 * q)) ≤ 1 - (B - c) ^ 2 / (4 * q) := by linarith
  have hpow := Real.rpow_le_rpow (Nat.cast_nonneg J) hx.1 (by norm_num : 0 ≤ (1 / 4 : ℝ))
  have hp := mul_le_mul hpow (Real.exp_le_exp.mpr he) (Real.exp_nonneg _)
    (Real.rpow_nonneg hx0 _)
  apply hp.trans_eq
  rw [sub_eq_add_neg, Real.exp_add]
  ring

/-- Finite root Gaussian sums are bounded by a continuous Gaussian integral. -/
theorem upper_root_gaussian_sum_integral (q c : ℝ) (M : ℕ) (hq : 1 ≤ q) :
    (∑ J ∈ Finset.range M, (J : ℝ) ^ (1 / 4 : ℝ) *
      Real.exp (-((Real.sqrt (2 * (J : ℝ)) - c) ^ 2 / (2 * q)))) ≤
    Real.exp 1 * ∫ x in (0 : ℝ)..(M : ℝ),
      x ^ (1 / 4 : ℝ) * Real.exp (-((Real.sqrt (2 * x) - c) ^ 2 / (4 * q))) := by
  let g := fun x : ℝ ↦ Real.exp 1 *
    (x ^ (1 / 4 : ℝ) * Real.exp (-((Real.sqrt (2 * x) - c) ^ 2 / (4 * q))))
  have hg : Continuous g := by dsimp [g]; fun_prop (disch := norm_num)
  have hh := sum_Ico_le_integral_of_le (a := 0) (b := M) (Nat.zero_le M)
    (f := fun x : ℝ ↦ x ^ (1 / 4 : ℝ) *
      Real.exp (-((Real.sqrt (2 * x) - c) ^ 2 / (2 * q))))
    (g := g) (fun J hJ x hx ↦ upper_root_gaussian_window q c J x hq (by simpa using hx))
    (hg.integrableOn_Icc.mono_set Ico_subset_Icc_self)
  simpa only [Nat.Ico_zero_eq_range, Nat.cast_zero, g,
    intervalIntegral.integral_const_mul] using hh

end SRWTightness
