import SRWTightness.EuclideanThirdMoment

open MeasureTheory

namespace SRWTightness

/-- A pointwise norm contraction transfers integrability and the exact cubic moment scale. -/
theorem third_moment_of_norm_le_div {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (X Y : Ω → EuclideanSpace ℝ ι) (hY : Measurable Y)
    (hiX : Integrable (fun ω ↦ ‖X ω‖ ^ 3) μ) (q : ℝ) (hq : 0 < q)
    (hb : ∀ ω, ‖Y ω‖ ≤ ‖X ω‖ / q) :
    Integrable (fun ω ↦ ‖Y ω‖ ^ 3) μ ∧
      (∫ ω, ‖Y ω‖ ^ 3 ∂μ) ≤ (∫ ω, ‖X ω‖ ^ 3 ∂μ) / q ^ 3 := by
  have hmajor := hiX.div_const (q ^ 3)
  have hm : Measurable (fun ω ↦ ‖Y ω‖ ^ 3) := by fun_prop
  have hpt (ω : Ω) : ‖Y ω‖ ^ 3 ≤ ‖X ω‖ ^ 3 / q ^ 3 := by
    simpa only [div_pow] using pow_le_pow_left₀ (norm_nonneg _) (hb ω) 3
  have hiY : Integrable (fun ω ↦ ‖Y ω‖ ^ 3) μ :=
    hmajor.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall (fun ω ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg _) _)]
      exact hpt ω))
  refine ⟨hiY, ?_⟩
  have hh := integral_mono hiY hmajor hpt
  rwa [integral_div] at hh

end SRWTightness
