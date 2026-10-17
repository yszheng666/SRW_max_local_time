import SRWTightness.SixthMomentFromExponential
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.Integral

open MeasureTheory

namespace SRWTightness

/-- For a nonnegative observation, centering costs at most twice its third raw moment. -/
theorem nonnegative_centered_third_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (hX0 : ∀ ω, 0 ≤ X ω) (hi3 : Integrable (fun ω ↦ X ω ^ 3) μ) :
    Integrable X μ ∧
    Integrable (fun ω ↦ |X ω - ∫ a, X a ∂μ| ^ 3) μ ∧
    (∫ ω, |X ω - ∫ a, X a ∂μ| ^ 3 ∂μ) ≤ 2 * (∫ ω, X ω ^ 3 ∂μ) := by
  have hsmall (ω : Ω) : X ω ≤ 1 + X ω ^ 3 := by
    by_cases hx : X ω ≤ 1
    · linarith [pow_nonneg (hX0 ω) 3]
    · have hh := pow_le_pow_right₀ (by linarith : 1 ≤ X ω) (by norm_num : 1 ≤ 3)
      simpa only [pow_one] using hh.trans (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1))
  have hiB1 : Integrable (fun ω ↦ 1 + X ω ^ 3) μ := (integrable_const 1).add hi3
  have hiX : Integrable X μ := hiB1.mono' hX.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hX0 ω)]
      exact hsmall ω))
  let m := ∫ a, X a ∂μ
  have hm0 : 0 ≤ m := integral_nonneg hX0
  have hm3 : m ^ 3 ≤ ∫ a, X a ^ 3 ∂μ :=
    (convexOn_pow (𝕜 := ℝ) 3).map_integral_le (by fun_prop) isClosed_Ici
      (Filter.Eventually.of_forall hX0) hiX hi3
  have hdom (ω : Ω) : |X ω - m| ^ 3 ≤ X ω ^ 3 + m ^ 3 := by
    by_cases hx : X ω ≤ m
    · rw [abs_of_nonpos (by linarith : X ω - m ≤ 0)]
      have hh := pow_le_pow_left₀ (by linarith : 0 ≤ -(X ω - m))
        (by linarith [hX0 ω] : -(X ω - m) ≤ m) 3
      linarith [pow_nonneg (hX0 ω) 3]
    · rw [abs_of_nonneg (by linarith : 0 ≤ X ω - m)]
      have hh := pow_le_pow_left₀ (by linarith : 0 ≤ X ω - m)
        (by linarith : X ω - m ≤ X ω) 3
      linarith [pow_nonneg hm0 3]
  have hiB : Integrable (fun ω ↦ X ω ^ 3 + m ^ 3) μ := hi3.add (integrable_const _)
  have hm : Measurable (fun ω ↦ |X ω - m| ^ 3) := by fun_prop
  have hiC : Integrable (fun ω ↦ |X ω - m| ^ 3) μ := hiB.mono' hm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) 3)]
      exact hdom ω))
  refine ⟨hiX, hiC, ?_⟩
  have hh := integral_mono hiC hiB hdom
  rw [integral_add hi3 (integrable_const _), integral_const] at hh
  simp only [probReal_univ, one_smul] at hh
  linarith

end SRWTightness
