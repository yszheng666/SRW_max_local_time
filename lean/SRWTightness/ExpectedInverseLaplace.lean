import SRWTightness.RadialInverseLaplace
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory
namespace SRWTightness

/-- An integrable positive reciprocal admits the exact iterated Gaussian Laplace formula. -/
theorem expected_inverse_laplace {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (R : Ω → ℝ) (hR : Measurable R)
    (hpos : ∀ᵐ ω ∂μ, 0 < R ω) (hint : Integrable (fun ω ↦ (R ω)⁻¹) μ) :
    (∫ ω, (R ω)⁻¹ ∂μ) = (2 / Real.sqrt Real.pi) *
      ∫ t in Set.Ioi (0 : ℝ), ∫ ω, Real.exp (-(t ^ 2) * (R ω) ^ 2) ∂μ := by
  let ν : Measure ℝ := volume.restrict (Set.Ioi 0)
  let F : Ω × ℝ → ℝ := fun p ↦ Real.exp (-(p.2 ^ 2) * (R p.1) ^ 2)
  have hm : Measurable F := by
    exact (((measurable_snd.pow_const 2).neg).mul
      ((hR.comp measurable_fst).pow_const 2)).exp
  have hv (ω : Ω) (hω : 0 < R ω) :
      (∫ t, F (ω, t) ∂ν) = (Real.sqrt Real.pi / 2) * (R ω)⁻¹ := by
    dsimp [F, ν]
    simp_rw [show ∀ t : ℝ, -(t ^ 2) * (R ω) ^ 2 = -((R ω) ^ 2) * t ^ 2
      by intro t; ring]
    rw [integral_gaussian_Ioi, Real.sqrt_div Real.pi_pos.le, Real.sqrt_sq hω.le]
    ring
  have hi : Integrable F (μ.prod ν) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
    constructor
    · filter_upwards [hpos] with ω hω
      have hg := (integrable_exp_neg_mul_sq (sq_pos_of_pos hω)).integrableOn
        (s := Set.Ioi (0 : ℝ))
      apply hg.congr
      filter_upwards [] with t
      dsimp [F]
      congr 1
      ring
    · apply (hint.const_mul (Real.sqrt Real.pi / 2)).congr
      filter_upwards [hpos] with ω hω
      have hn (t : ℝ) : ‖F (ω, t)‖ = F (ω, t) :=
        Real.norm_of_nonneg (Real.exp_pos _).le
      simp_rw [hn]
      exact (hv ω hω).symm
  have he : (∫ ω, ∫ t, F (ω, t) ∂ν ∂μ) =
      (Real.sqrt Real.pi / 2) * ∫ ω, (R ω)⁻¹ ∂μ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hpos] with ω hω
    exact hv ω hω
  have hs := integral_integral_swap (f := fun ω t ↦ F (ω, t)) hi
  rw [he] at hs
  change (∫ ω, (R ω)⁻¹ ∂μ) = (2 / Real.sqrt Real.pi) *
    ∫ t, ∫ ω, F (ω, t) ∂μ ∂ν
  rw [← hs]
  have hp : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  field_simp

end SRWTightness
