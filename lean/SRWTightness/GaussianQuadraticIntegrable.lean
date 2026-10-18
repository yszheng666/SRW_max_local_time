import SRWTightness.GaussianEventLower

open Matrix MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace SRWTightness

theorem gaussianCoordinateLaw_coordinate_memLp_two {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) (i : ι) :
    MemLp (fun x : ι → ℝ ↦ x i) 2 (gaussianCoordinateLaw K) := by
  unfold gaussianCoordinateLaw
  apply (memLp_map_measure_iff (measurable_pi_apply i).aestronglyMeasurable (by fun_prop)).mpr
  have hh := (innerSL ℝ (EuclideanSpace.basisFun ι ℝ i)).comp_memLp'
    (IsGaussian.memLp_two_id (μ := multivariateGaussian 0 K))
  simpa [Function.comp_def, PiLp.inner_apply] using hh

theorem gaussianInverseCorrection_integrable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K S : Matrix ι ι ℝ) : Integrable (gaussianInverseCorrection K S) (gaussianCoordinateLaw K) := by
  unfold gaussianInverseCorrection
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply integrable_finset_sum
  intro i _
  apply integrable_finset_sum
  intro j _
  have hh := ((gaussianCoordinateLaw_coordinate_memLp_two K i).integrable_mul
    (gaussianCoordinateLaw_coordinate_memLp_two K j)).const_mul ((S⁻¹ - K⁻¹) i j)
  simpa only [Pi.mul_apply, mul_left_comm] using hh

end SRWTightness
