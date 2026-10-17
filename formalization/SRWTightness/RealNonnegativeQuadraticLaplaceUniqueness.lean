import SRWTightness.NonnegativeQuadraticLaplaceUniqueness

open MeasureTheory
namespace SRWTightness

/-- Integer quadratic Laplace values determine finite real measures supported
on nonnegative values. -/
theorem real_nonnegative_quadratic_laplace_uniqueness (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) (hν : ∀ᵐ x ∂ν, 0 ≤ x)
    (h : ∀ n : ℕ, (∫ x : ℝ, Real.exp (-(n : ℝ) * x ^ 2) ∂μ) =
      ∫ x : ℝ, Real.exp (-(n : ℝ) * x ^ 2) ∂ν) : μ = ν := by
  have hm (ρ : Measure ℝ) (hρ : ∀ᵐ x ∂ρ, 0 ≤ x) (n : ℕ) :
      (∫ x : NNReal, Real.exp (-(n : ℝ) * (x : ℝ) ^ 2) ∂ρ.map Real.toNNReal) =
        ∫ x : ℝ, Real.exp (-(n : ℝ) * x ^ 2) ∂ρ := by
    rw [integral_map measurable_real_toNNReal.aemeasurable
      (by fun_prop : AEStronglyMeasurable
        (fun x : NNReal ↦ Real.exp (-(n : ℝ) * (x : ℝ) ^ 2)) (ρ.map Real.toNNReal))]
    apply integral_congr_ae
    filter_upwards [hρ] with x hx
    rw [Real.coe_toNNReal x hx]
  have he := nonnegative_quadratic_laplace_uniqueness
    (μ.map Real.toNNReal) (ν.map Real.toNNReal) (fun n ↦ by rw [hm μ hμ n, hm ν hν n, h n])
  have hback (ρ : Measure ℝ) (hρ : ∀ᵐ x ∂ρ, 0 ≤ x) :
      (ρ.map Real.toNNReal).map ((↑) : NNReal → ℝ) = ρ := by
    rw [Measure.map_map measurable_coe_nnreal_real measurable_real_toNNReal]
    calc
      _ = ρ.map id := Measure.map_congr (by
        filter_upwards [hρ] with x hx
        exact Real.coe_toNNReal x hx)
      _ = ρ := Measure.map_id
  have hh := congrArg (fun ρ : Measure NNReal ↦ ρ.map ((↑) : NNReal → ℝ)) he
  simpa only [hback μ hμ, hback ν hν] using hh

end SRWTightness
