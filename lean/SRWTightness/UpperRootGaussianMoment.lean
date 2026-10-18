import SRWTightness.UpperRootGaussianWindow
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

open MeasureTheory

namespace SRWTightness

/-- A shifted weighted Gaussian used to bound the continuous root-number integral. -/
noncomputable def upperRootGaussianMoment (q c y : ℝ) : ℝ :=
  (|y| + 1) ^ (3 / 2 : ℝ) * Real.exp (-((y - c) ^ 2 / q))

/-- Scaling around the Gaussian center gives a fixed polynomial Gaussian majorant. -/
theorem upper_root_gaussian_moment_scaled (q c z : ℝ) (hq : 1 ≤ q)
    (hc : 0 ≤ c) (hcap : c ≤ 3 * q) :
    upperRootGaussianMoment q c (Real.sqrt q * z + c) ≤
      32 * q ^ (3 / 2 : ℝ) * ((1 + z ^ 2) * Real.exp (-z ^ 2)) := by
  have hq0 : 0 < q := by linarith
  have hs : Real.sqrt q ≤ q := Real.sqrt_le_self_iff.mpr (Or.inr hq)
  have hab := abs_add_le (Real.sqrt q * z) c
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hc] at hab
  have hbound : |Real.sqrt q * z + c| + 1 ≤ q * (4 + |z|) := by
    have hm := mul_le_mul_of_nonneg_right hs (abs_nonneg z)
    nlinarith
  have hw := Real.rpow_le_rpow (by positivity : 0 ≤ |Real.sqrt q * z + c| + 1)
    hbound (by norm_num : 0 ≤ (3 / 2 : ℝ))
  rw [Real.mul_rpow hq0.le (by positivity)] at hw
  have hp : (4 + |z|) ^ (3 / 2 : ℝ) ≤ (4 + |z|) ^ 2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le
      (by linarith [abs_nonneg z] : 1 ≤ 4 + |z|) (by norm_num : (3 / 2 : ℝ) ≤ 2)
  have hpoly : (4 + |z|) ^ 2 ≤ 32 * (1 + z ^ 2) := by
    nlinarith [sq_abs z, sq_nonneg (|z| - 1)]
  have hweight := hw.trans (mul_le_mul_of_nonneg_left (hp.trans hpoly)
    (Real.rpow_nonneg hq0.le (3 / 2 : ℝ)))
  have he : -((Real.sqrt q * z + c - c) ^ 2 / q) = -z ^ 2 := by
    rw [add_sub_cancel_right, mul_pow, Real.sq_sqrt hq0.le]
    simp [hq0.ne']
  unfold upperRootGaussianMoment
  rw [he]
  exact (mul_le_mul_of_nonneg_right hweight (Real.exp_nonneg _)).trans_eq (by ring)

/-- The continuous root Gaussian moment has a uniform quadratic scale bound. -/
theorem upper_root_gaussian_moment_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ q c : ℝ, 1 ≤ q → 0 ≤ c → c ≤ 3 * q →
      Integrable (upperRootGaussianMoment q c) ∧
        (∫ y : ℝ, upperRootGaussianMoment q c y) ≤ K * q ^ 2 := by
  let G := fun z : ℝ ↦ (1 + z ^ 2) * Real.exp (-z ^ 2)
  have h0 : Integrable (fun z : ℝ ↦ Real.exp (-z ^ 2)) := by
    simpa only [neg_mul, one_mul] using integrable_exp_neg_mul_sq (b := 1) (by norm_num)
  have h2 : Integrable (fun z : ℝ ↦ z ^ 2 * Real.exp (-z ^ 2)) := by
    simpa only [Real.rpow_two, neg_mul, one_mul] using
      integrable_rpow_mul_exp_neg_mul_sq (b := 1) (s := 2) (by norm_num) (by norm_num)
  have hG : Integrable G := by
    apply (h0.add h2).congr
    filter_upwards [] with z
    dsimp [G]
    ring
  have hG0 : 0 ≤ ∫ z : ℝ, G z := integral_nonneg (fun _ ↦ by dsimp [G]; positivity)
  refine ⟨32 * ((∫ z : ℝ, G z) + 1), by positivity, ?_⟩
  intro q c hq hc hcap
  have hq0 : 0 < q := by linarith
  have hs0 : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
  let H := upperRootGaussianMoment q c
  have hcont : Continuous (fun z : ℝ ↦ H (Real.sqrt q * z + c)) := by
    dsimp [H, upperRootGaussianMoment]
    fun_prop (disch := norm_num)
  have hscaled : Integrable (fun z : ℝ ↦ H (Real.sqrt q * z + c)) := by
    apply (hG.const_mul (32 * q ^ (3 / 2 : ℝ))).mono' hcont.aestronglyMeasurable
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [H, upperRootGaussianMoment]; positivity)]
    exact upper_root_gaussian_moment_scaled q c z hq hc hcap
  have hshift : Integrable (fun y : ℝ ↦ H (y + c)) := by
    apply (hscaled.comp_mul_left' (R := (Real.sqrt q)⁻¹) (inv_ne_zero hs0.ne')).congr
    filter_upwards [] with y
    simp only [← mul_assoc, mul_inv_cancel₀ hs0.ne', one_mul]
  have hH : Integrable H := by
    apply (hshift.comp_add_right (-c)).congr
    filter_upwards [] with y
    simp only [add_assoc, neg_add_cancel, add_zero]
  refine ⟨hH, ?_⟩
  have hI := integral_mono hscaled (hG.const_mul (32 * q ^ (3 / 2 : ℝ)))
    (fun z ↦ upper_root_gaussian_moment_scaled q c z hq hc hcap)
  rw [integral_const_mul] at hI
  have hchange := Measure.integral_comp_mul_left (fun y : ℝ ↦ H (y + c)) (Real.sqrt q)
  rw [integral_add_right_eq_self] at hchange
  simp only [smul_eq_mul, abs_of_pos (inv_pos.mpr hs0)] at hchange
  have hfactor : Real.sqrt q * q ^ (3 / 2 : ℝ) = q ^ 2 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hq0]
    norm_num
  calc
    _ = Real.sqrt q * (∫ z : ℝ, H (Real.sqrt q * z + c)) := by
      rw [hchange, ← mul_assoc, mul_inv_cancel₀ hs0.ne', one_mul]
    _ ≤ Real.sqrt q * (32 * q ^ (3 / 2 : ℝ) * ∫ z : ℝ, G z) :=
      mul_le_mul_of_nonneg_left hI hs0.le
    _ = 32 * (∫ z : ℝ, G z) * (Real.sqrt q * q ^ (3 / 2 : ℝ)) := by ring
    _ = 32 * (∫ z : ℝ, G z) * q ^ 2 := by rw [hfactor]
    _ ≤ _ := by nlinarith [sq_nonneg q]

end SRWTightness
