import SRWTightness.NonnegativeCenteredThirdMoment

open MeasureTheory

namespace SRWTightness

/-- Centering an arbitrary real observation costs at most eight times its third absolute moment. -/
theorem signed_centered_third_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (hi3 : Integrable (fun ω ↦ |X ω| ^ 3) μ) :
    Integrable X μ ∧
    Integrable (fun ω ↦ |X ω - ∫ a, X a ∂μ| ^ 3) μ ∧
    (∫ ω, |X ω - ∫ a, X a ∂μ| ^ 3 ∂μ) ≤ 8 * (∫ ω, |X ω| ^ 3 ∂μ) := by
  have hiA := (nonnegative_centered_third_moment μ (fun ω ↦ |X ω|)
    (by fun_prop) (fun ω ↦ abs_nonneg _) hi3).1
  have hiX : Integrable X μ := hiA.mono' hX.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω ↦ by simp only [Real.norm_eq_abs, le_refl]))
  let m := ∫ a, X a ∂μ
  have hm3 : |m| ^ 3 ≤ ∫ a, |X a| ^ 3 ∂μ := by
    calc
      _ ≤ (∫ a, |X a| ∂μ) ^ 3 :=
        pow_le_pow_left₀ (abs_nonneg _) abs_integral_le_integral_abs 3
      _ ≤ _ := (convexOn_pow (𝕜 := ℝ) 3).map_integral_le (by fun_prop) isClosed_Ici
        (Filter.Eventually.of_forall (fun a ↦ abs_nonneg (X a))) hiA hi3
  have hdom (ω : Ω) : |X ω - m| ^ 3 ≤ 4 * (|X ω| ^ 3 + |m| ^ 3) := by
    have hh := pow_le_pow_left₀ (abs_nonneg (X ω - m)) (abs_sub _ _) 3
    have hp : 0 ≤ (|X ω| - |m|) ^ 2 * (|X ω| + |m|) := by positivity
    nlinarith
  have hiB : Integrable (fun ω ↦ 4 * (|X ω| ^ 3 + |m| ^ 3)) μ :=
    (hi3.add (integrable_const _)).const_mul _
  have hiC : Integrable (fun ω ↦ |X ω - m| ^ 3) μ := hiB.mono'
    (by fun_prop) (Filter.Eventually.of_forall (fun ω ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) 3)]
      exact hdom ω))
  refine ⟨hiX, hiC, ?_⟩
  have hh := integral_mono hiC hiB hdom
  rw [integral_const_mul, integral_add hi3 (integrable_const _), integral_const] at hh
  simp only [probReal_univ, one_smul] at hh
  linarith

end SRWTightness
