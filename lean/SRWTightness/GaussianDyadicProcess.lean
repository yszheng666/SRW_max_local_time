import SRWTightness.GaussianSeriesContinuity
import Mathlib.MeasureTheory.Constructions.Polish.Basic

open MeasureTheory ProbabilityTheory

namespace SRWTightness

theorem gaussianDyadicPath_joint_measurable :
    Measurable (fun p : GaussianCoefficientSpace × ℝ ↦ gaussianDyadicPath p.1 p.2) := by
  unfold gaussianDyadicPath schauderLevel scaledSchauderTent
  apply Measurable.add
  · exact measurable_snd.mul ((measurable_pi_apply none).comp measurable_fst)
  · apply Measurable.tsum
    intro n
    apply Finset.measurable_sum
    intro k hk
    exact ((measurable_pi_apply (some (n, k))).comp measurable_fst).mul
      (measurable_const.mul (schauderTent_continuous.measurable.comp
        ((measurable_const.mul measurable_snd).sub measurable_const)))

theorem gaussianDyadicPath_measurable (t : ℝ) :
    Measurable (fun ω ↦ gaussianDyadicPath ω t) :=
  gaussianDyadicPath_joint_measurable.comp (measurable_id.prodMk measurable_const)

theorem gaussianDyadicPath_zero (ω : GaussianCoefficientSpace) :
    gaussianDyadicPath ω 0 = 0 := by
  have h : ∀ n : ℕ, schauderLevel (2 ^ n) ((2 : ℝ) ^ n)
      ((Real.sqrt 2)⁻¹ ^ n) (fun k ↦ ω (some (n, k))) 0 = 0 := by
    intro n
    apply Finset.sum_eq_zero
    intro k hk
    have hz := schauderTent_eq_zero_left (((2 : ℝ) ^ n) * 0 - k) (by simp)
    unfold scaledSchauderTent
    rw [hz, mul_zero, mul_zero]
  simp only [gaussianDyadicPath, h, tsum_zero, zero_mul, add_zero]

theorem gaussianDyadicPath_one (ω : GaussianCoefficientSpace) :
    gaussianDyadicPath ω 1 = ω none := by
  have h : ∀ n : ℕ, schauderLevel (2 ^ n) ((2 : ℝ) ^ n)
      ((Real.sqrt 2)⁻¹ ^ n) (fun k ↦ ω (some (n, k))) 1 = 0 := by
    intro n
    apply Finset.sum_eq_zero
    intro k hk
    have hk' : k + 1 ≤ 2 ^ n := Finset.mem_range.mp hk
    have hk'' : (k : ℝ) + 1 ≤ (2 : ℝ) ^ n := by exact_mod_cast hk'
    have hz := schauderTent_eq_zero_right (((2 : ℝ) ^ n) * 1 - k) (by linarith)
    unfold scaledSchauderTent
    rw [hz, mul_zero, mul_zero]
  simp only [gaussianDyadicPath, h, tsum_zero, one_mul, add_zero]

theorem gaussianDyadicPath_endpoint_law :
    gaussianCoefficientLaw.map (fun ω ↦ gaussianDyadicPath ω 1) = gaussianReal 0 1 := by
  simp only [gaussianDyadicPath_one]
  exact gaussianCoefficient_map none

end SRWTightness
