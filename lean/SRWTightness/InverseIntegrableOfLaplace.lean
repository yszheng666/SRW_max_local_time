import SRWTightness.ExpectedInverseLaplace

open MeasureTheory
namespace SRWTightness

/-- Integrability of the averaged positive Gaussian Laplace weights controls the reciprocal. -/
theorem inverse_integrable_of_laplace {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (R : Ω → ℝ) (hR : Measurable R)
    (hpos : ∀ᵐ ω ∂μ, 0 < R ω)
    (hint : IntegrableOn (fun t : ℝ ↦ ∫ ω, Real.exp (-(t ^ 2) * (R ω) ^ 2) ∂μ)
      (Set.Ioi 0)) : Integrable (fun ω ↦ (R ω)⁻¹) μ := by
  let ν : Measure ℝ := volume.restrict (Set.Ioi 0)
  let F : Ω × ℝ → ℝ := fun p ↦ Real.exp (-(p.2 ^ 2) * (R p.1) ^ 2)
  have hm : Measurable F := by
    exact (((measurable_snd.pow_const 2).neg).mul
      ((hR.comp measurable_fst).pow_const 2)).exp
  have hi : Integrable F (μ.prod ν) := by
    apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
    constructor
    · filter_upwards [] with t
      have hmt := hm.comp (measurable_id.prodMk (measurable_const (a := t)))
      apply Integrable.of_bound hmt.aestronglyMeasurable 1
      filter_upwards [] with ω
      change ‖Real.exp (-(t ^ 2) * (R ω) ^ 2)‖ ≤ 1
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg t)) (sq_nonneg _)
    · apply hint.congr
      filter_upwards [] with t
      apply integral_congr_ae
      filter_upwards [] with ω
      exact (Real.norm_of_nonneg (Real.exp_pos _).le).symm
  have hh := hi.integral_prod_left.const_mul (2 / Real.sqrt Real.pi)
  apply hh.congr
  filter_upwards [hpos] with ω hω
  have hv := inverse_sqrt_gaussian_integral ((R ω) ^ 2) (sq_pos_of_pos hω)
  rw [Real.sqrt_sq hω.le] at hv
  rw [hv]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  dsimp [F]
  congr 1
  ring

end SRWTightness
