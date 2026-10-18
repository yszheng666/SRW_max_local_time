import SRWTightness.TiltedMeanDerivative

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The third joint centered moment equals the covariance response polynomial. -/
theorem joint_centered_third_covariance_identity {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H J X : Ω → ℝ)
    (hH : Integrable H μ) (hJ : Integrable J μ) (hX : Integrable X μ)
    (hHJ : Integrable (fun ω ↦ H ω * J ω) μ)
    (hHX : Integrable (fun ω ↦ H ω * X ω) μ)
    (hJX : Integrable (fun ω ↦ J ω * X ω) μ)
    (hHJX : Integrable (fun ω ↦ H ω * J ω * X ω) μ) :
    (∫ ω, (H ω - ∫ a, H a ∂μ) * (J ω - ∫ a, J a ∂μ) * (X ω - ∫ a, X a ∂μ) ∂μ) =
      covariance (fun ω ↦ H ω * J ω) X μ - covariance H X μ * (∫ a, J a ∂μ) -
        (∫ a, H a ∂μ) * covariance J X μ := by
  let h := ∫ a, H a ∂μ
  let j := ∫ a, J a ∂μ
  let x := ∫ a, X a ∂μ
  have hn2 : Integrable (fun ω ↦ h * (J ω * X ω) + j * (H ω * X ω)) μ :=
    (hJX.const_mul h).add (hHX.const_mul j)
  have hn : Integrable
      (fun ω ↦ (h * (J ω * X ω) + j * (H ω * X ω)) + x * (H ω * J ω)) μ :=
    hn2.add (hHJ.const_mul x)
  have hp2 : Integrable (fun ω ↦ (h * j) * X ω + (h * x) * J ω) μ :=
    (hX.const_mul (h * j)).add (hJ.const_mul (h * x))
  have hp : Integrable
      (fun ω ↦ ((h * j) * X ω + (h * x) * J ω) + (j * x) * H ω) μ :=
    hp2.add (hH.const_mul (j * x))
  have hm : Integrable (fun ω ↦ H ω * J ω * X ω -
      ((h * (J ω * X ω) + j * (H ω * X ω)) + x * (H ω * J ω))) μ := hHJX.sub hn
  have ha : Integrable (fun ω ↦ (H ω * J ω * X ω -
      ((h * (J ω * X ω) + j * (H ω * X ω)) + x * (H ω * J ω))) +
      (((h * j) * X ω + (h * x) * J ω) + (j * x) * H ω)) μ := hm.add hp
  have he : (fun ω ↦ (H ω - h) * (J ω - j) * (X ω - x)) =
      (fun ω ↦ ((H ω * J ω * X ω -
        ((h * (J ω * X ω) + j * (H ω * X ω)) + x * (H ω * J ω))) +
        (((h * j) * X ω + (h * x) * J ω) + (j * x) * H ω)) - h * j * x) := by
    funext ω
    ring
  change (∫ ω, (H ω - h) * (J ω - j) * (X ω - x) ∂μ) = _
  rw [he, integral_sub ha (integrable_const _), integral_add hm hp,
    integral_sub hHJX hn, integral_add hn2 (hHJ.const_mul x),
    integral_add (hJX.const_mul h) (hHX.const_mul j),
    integral_add hp2 (hH.const_mul (j * x)),
    integral_add (hX.const_mul (h * j)) (hJ.const_mul (h * x))]
  simp only [integral_const_mul, integral_const, probReal_univ, one_smul]
  rw [covariance_eq_sub_of_integrable μ _ X hHJ hX hHJX,
    covariance_eq_sub_of_integrable μ H X hH hX hHX,
    covariance_eq_sub_of_integrable μ J X hJ hX hJX]
  dsimp only [h, j, x]
  ring

end SRWTightness
