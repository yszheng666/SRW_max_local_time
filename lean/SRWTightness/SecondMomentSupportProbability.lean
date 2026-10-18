import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory
namespace SRWTightness

/-- The second-moment lower bound for the probability of a set supporting an integrable
random variable. The proof integrates a nonnegative square. -/
theorem second_moment_support_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (S : Set Ω)
    (hS : NullMeasurableSet S μ) (hf : Integrable f μ)
    (hf₂ : Integrable (fun ω ↦ f ω ^ 2) μ)
    (hsupport : ∀ ω, ω ∉ S → f ω = 0)
    (c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hmean : c ≤ ∫ ω, f ω ∂μ) (hsecond : (∫ ω, f ω ^ 2 ∂μ) ≤ C) :
    c ^ 2 / C ≤ μ.real S := by
  classical
  let q := c / C
  let g := S.indicator (fun _ : Ω ↦ (1 : ℝ))
  have hg : Integrable g μ := (integrable_const 1).indicator₀ hS
  have hgint : (∫ ω, g ω ∂μ) = μ.real S := by
    dsimp [g]
    rw [integral_indicator₀ hS]
    simp
  have he (ω : Ω) : (q * f ω - g ω) ^ 2 =
      q ^ 2 * f ω ^ 2 - (2 * q) * f ω + g ω := by
    by_cases hs : ω ∈ S
    · simp only [g, Set.indicator_of_mem hs]
      ring
    · simp [g, hs, hsupport ω hs]
  have hnon : 0 ≤ q ^ 2 * (∫ ω, f ω ^ 2 ∂μ) -
      (2 * q) * (∫ ω, f ω ∂μ) + μ.real S := by
    have hh : 0 ≤ ∫ ω, (q * f ω - g ω) ^ 2 ∂μ :=
      integral_nonneg (fun ω ↦ sq_nonneg (q * f ω - g ω))
    simp_rw [he] at hh
    have hij : Integrable (fun ω ↦ q ^ 2 * f ω ^ 2 - (2 * q) * f ω) μ :=
      (hf₂.const_mul (q ^ 2)).sub (hf.const_mul (2 * q))
    rw [integral_add hij hg,
      integral_sub (hf₂.const_mul (q ^ 2)) (hf.const_mul (2 * q)), integral_const_mul,
      integral_const_mul, hgint] at hh
    exact hh
  have hm := mul_le_mul_of_nonneg_left hmean (show 0 ≤ 2 * q by dsimp [q]; positivity)
  have hs := mul_le_mul_of_nonneg_left hsecond (sq_nonneg q)
  have hpoly : 0 ≤ q ^ 2 * C - 2 * q * c + μ.real S := by
    linarith only [hnon, hm, hs]
  have hcancel : q ^ 2 * C - 2 * q * c = -(c ^ 2 / C) := by
    dsimp [q]
    field_simp
    <;> ring
  rw [hcancel] at hpoly
  linarith only [hpoly]

/-- Positive first moment and bounded second moment give a positive-event probability bound. -/
theorem second_moment_positive_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : Integrable f μ) (hf₂ : Integrable (fun ω ↦ f ω ^ 2) μ)
    (hf0 : ∀ ω, 0 ≤ f ω) (c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hmean : c ≤ ∫ ω, f ω ∂μ) (hsecond : (∫ ω, f ω ^ 2 ∂μ) ≤ C) :
    c ^ 2 / C ≤ μ.real {ω | 0 < f ω} := by
  apply second_moment_support_probability μ f {ω | 0 < f ω}
    (nullMeasurableSet_lt aemeasurable_const hf.aemeasurable) hf hf₂
    (fun ω hω ↦ le_antisymm (le_of_not_gt hω) (hf0 ω)) c C hc hC hmean hsecond

end SRWTightness
