import SRWTightness.ThirdCgfDerivative
import Mathlib.Probability.Moments.Tilted

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace SRWTightness

/-- Polynomial moments of the actual exponentially tilted law. -/
theorem integral_pow_tilted_mgf {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (t : ℝ) (n : ℕ) :
    (∫ ω, X ω ^ n ∂μ.tilted (fun ω ↦ t * X ω)) =
      (∫ ω, X ω ^ n * Real.exp (t * X ω) ∂μ) / mgf X μ t := by
  rw [integral_tilted_mul_eq_mgf, ← integral_div]
  congr 1
  funext ω
  simp only [smul_eq_mul]
  ring

/-- The third cgf derivative is the third centered moment under the actual tilted law. -/
theorem iteratedDeriv_three_cgf_eq_centered_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (t : ℝ)
    (ht : t ∈ interior (integrableExpSet X μ)) :
    let ν := μ.tilted (fun ω ↦ t * X ω)
    iteratedDeriv 3 (cgf X μ) t = ∫ ω, (X ω - ∫ a, X a ∂ν) ^ 3 ∂ν := by
  let ν := μ.tilted (fun ω ↦ t * X ω)
  have hi := interior_subset (s := integrableExpSet X μ) ht
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_tilted hi
  have hp (n : ℕ) : Integrable (fun ω ↦ X ω ^ n) ν := by
    apply (integrable_tilted_iff hi _).mpr
    simpa only [smul_eq_mul, mul_comm] using
      integrable_pow_mul_exp_of_mem_interior_integrableExpSet ht n
  have hiX : Integrable X ν := by simpa only [pow_one] using hp 1
  let m := ∫ a, X a ∂ν
  have hpoly : (fun ω ↦ (X ω - m) ^ 3) =
      (fun ω ↦ (X ω ^ 3 - (3 * m) * X ω ^ 2) + (3 * m ^ 2) * X ω - m ^ 3) := by
    funext ω
    ring
  change iteratedDeriv 3 (cgf X μ) t = ∫ ω, (X ω - m) ^ 3 ∂ν
  have hq : Integrable (fun ω ↦ X ω ^ 3 - (3 * m) * X ω ^ 2) ν :=
    (hp 3).sub ((hp 2).const_mul (3 * m))
  have hr : Integrable
      (fun ω ↦ (X ω ^ 3 - (3 * m) * X ω ^ 2) + (3 * m ^ 2) * X ω) ν :=
    hq.add (hiX.const_mul (3 * m ^ 2))
  rw [hpoly, integral_sub hr (integrable_const (m ^ 3)),
    integral_add hq (hiX.const_mul (3 * m ^ 2)),
    integral_sub (hp 3) ((hp 2).const_mul (3 * m))]
  simp only [integral_const_mul, integral_const, probReal_univ, one_smul]
  change iteratedDeriv 3 (cgf X μ) t =
    (∫ ω, X ω ^ 3 ∂ν) - 3 * m * (∫ ω, X ω ^ 2 ∂ν) + 3 * m ^ 2 * m - m ^ 3
  have hm : m = (∫ ω, X ω * Real.exp (t * X ω) ∂μ) / mgf X μ t := by
    simpa only [pow_one] using integral_pow_tilted_mgf μ X t 1
  rw [iteratedDeriv_three_cgf_formula μ X t ht, hm]
  dsimp only [ν]
  rw [integral_pow_tilted_mgf, integral_pow_tilted_mgf]
  ring

end SRWTightness
