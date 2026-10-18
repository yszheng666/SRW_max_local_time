import SRWTightness.GaussianField
import SRWTightness.GaussianProductDensity

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped MatrixOrder

namespace SRWTightness

 theorem multivariateGaussian_zero_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) :
    multivariateGaussian 0 G = (Measure.pi (fun _ : ι ↦ gaussianReal 0 1)).map
      (fun x : ι → ℝ ↦ toLp 2 ((CFC.sqrt G).mulVec x)) := by
  rw [multivariateGaussian, ← map_pi_eq_stdGaussian,
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  simp

 theorem integral_multivariateGaussian_quadratic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (f c : ι → ℝ) :
    (∫ φ : EuclideanSpace ℝ ι, Real.exp (-(∑ i, f i * (φ i + c i) ^ 2) / 2)
      ∂multivariateGaussian 0 G) =
      ∫ x : ι → ℝ, Real.exp (-(∑ i, f i * ((CFC.sqrt G).mulVec x i + c i) ^ 2) / 2)
        ∂Measure.pi (fun _ : ι ↦ gaussianReal 0 1) := by
  rw [multivariateGaussian_zero_pi]
  have hm : Measurable (fun x : ι → ℝ ↦ toLp 2 ((CFC.sqrt G).mulVec x)) := by
    change Measurable (fun x : ι → ℝ ↦ toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt G) (toLp 2 x))
    fun_prop
  rw [integral_map hm.aemeasurable (by fun_prop)]

 theorem matrix_sqrt_symmetric {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) : (CFC.sqrt G).transpose = CFC.sqrt G := by
  have h := (CFC.sqrt_nonneg G).isSelfAdjoint.isHermitian
  ext i j
  have he := congrArg (fun M : Matrix ι ι ℝ ↦ M i j) h.eq
  simpa only [Matrix.conjTranspose_apply, star_trivial, Matrix.transpose_apply] using he

 theorem matrix_sqrt_square {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (hG : G.PosSemidef) : CFC.sqrt G * CFC.sqrt G = G :=
  CFC.sqrt_mul_sqrt_self G hG.nonneg

end SRWTightness
