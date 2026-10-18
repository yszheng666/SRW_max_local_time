import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic

open MeasureTheory

namespace SRWTightness

/-- The normalized quadratic Gaussian kernel for terminal unit-window sums. -/
noncomputable def upperTerminalGaussianKernel (d c x : ℝ) : ℝ :=
  (1 + (x / Real.sqrt d) ^ 2) / Real.sqrt d * Real.exp (-c * x ^ 2 / d)

/-- Gaussian scaling makes the total integral of the normalized terminal kernel independent of d. -/
theorem upper_terminal_gaussian_integral (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℝ, 0 < d →
      Integrable (upperTerminalGaussianKernel d c) ∧
        (∫ x : ℝ, upperTerminalGaussianKernel d c x) ≤ C := by
  let G := fun z : ℝ ↦ (1 + z ^ 2) * Real.exp (-c * z ^ 2)
  have h0 : Integrable (fun z : ℝ ↦ Real.exp (-c * z ^ 2)) :=
    integrable_exp_neg_mul_sq hc
  have h2 : Integrable (fun z : ℝ ↦ z ^ 2 * Real.exp (-c * z ^ 2)) := by
    simpa only [Real.rpow_two] using
      integrable_rpow_mul_exp_neg_mul_sq (b := c) (s := 2) hc (by norm_num)
  have hG : Integrable G := by
    apply (h0.add h2).congr
    filter_upwards [] with z
    dsimp [G]
    ring
  have hG0 : 0 ≤ ∫ z : ℝ, G z := integral_nonneg (fun _ ↦ by dsimp [G]; positivity)
  refine ⟨(∫ z : ℝ, G z) + 1, by positivity, ?_⟩
  intro d hd
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
  have hi : Integrable (fun x : ℝ ↦ (Real.sqrt d)⁻¹ * G ((Real.sqrt d)⁻¹ * x)) :=
    (hG.comp_mul_left' (R := (Real.sqrt d)⁻¹) (inv_ne_zero hs.ne')).const_mul _
  have he (x : ℝ) : upperTerminalGaussianKernel d c x =
      (Real.sqrt d)⁻¹ * G ((Real.sqrt d)⁻¹ * x) := by
    have hex : -c * x ^ 2 / d = -c * ((Real.sqrt d)⁻¹ * x) ^ 2 := by
      rw [mul_pow, inv_pow, Real.sq_sqrt hd.le]
      ring
    dsimp [upperTerminalGaussianKernel, G]
    rw [hex]
    ring
  have hI : Integrable (upperTerminalGaussianKernel d c) := by
    simpa only [funext he] using hi
  refine ⟨hI, ?_⟩
  have hchange := Measure.integral_comp_mul_left G ((Real.sqrt d)⁻¹)
  simp only [inv_inv, abs_of_pos hs, smul_eq_mul] at hchange
  calc
    _ = (Real.sqrt d)⁻¹ * ∫ x : ℝ, G ((Real.sqrt d)⁻¹ * x) := by
      simp_rw [he]
      rw [integral_const_mul]
    _ = ∫ z : ℝ, G z := by
      rw [hchange, ← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]
    _ ≤ _ := by linarith

end SRWTightness
