import SRWTightness.GaussianMeanLaw

open MeasureTheory ProbabilityTheory Matrix

namespace SRWTightness

noncomputable def gaussianMeanDensityWeight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℝ) (K : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  Real.exp (m ⬝ᵥ (K⁻¹ *ᵥ x) - (m ⬝ᵥ (K⁻¹ *ᵥ m)) / 2)

/-- The likelihood ratio for a Gaussian mean shift is measurable. -/
theorem gaussianMeanDensityWeight_measurable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℝ) (K : Matrix ι ι ℝ) : Measurable (gaussianMeanDensityWeight m K) := by
  unfold gaussianMeanDensityWeight
  simp only [dotProduct, Matrix.mulVec]
  fun_prop

/-- Exact completion of the square for a Gaussian mean shift. -/
theorem gaussian_mean_shift_quadratic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m x : ι → ℝ) (K : Matrix ι ι ℝ) (hK : K.PosDef) :
    (x - m) ⬝ᵥ (K⁻¹ *ᵥ (x - m)) =
      x ⬝ᵥ (K⁻¹ *ᵥ x) - 2 * (m ⬝ᵥ (K⁻¹ *ᵥ x)) + m ⬝ᵥ (K⁻¹ *ᵥ m) := by
  have hT : (K⁻¹)ᵀ = K⁻¹ := by
    rw [Matrix.transpose_nonsing_inv]
    congr 1
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hK.isHermitian.eq
  have hcross : x ⬝ᵥ (K⁻¹ *ᵥ m) = m ⬝ᵥ (K⁻¹ *ᵥ x) := by
    simpa only [hT] using Matrix.dotProduct_transpose_mulVec K⁻¹ x m
  rw [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct, hcross]
  ring

/-- The shifted Lebesgue density equals the original Gaussian density times its mean likelihood ratio. -/
theorem gaussianMeanCovarianceDensity_mul_weight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℝ) (K : Matrix ι ι ℝ) (hK : K.PosDef) (x : ι → ℝ) :
    gaussianCovarianceDensity K (x - m) = gaussianCovarianceDensity K x *
      ENNReal.ofReal (gaussianMeanDensityWeight m K x) := by
  have hp := gaussianCovarianceDensity_toReal_pos K hK x
  have hs := gaussianCovarianceDensity_toReal_pos K hK (x - m)
  have he : (gaussianCovarianceDensity K (x - m)).toReal =
      (gaussianCovarianceDensity K x).toReal * gaussianMeanDensityWeight m K x := by
    rw [gaussianCovarianceDensity_toReal K hK, gaussianCovarianceDensity_toReal K hK,
      gaussian_mean_shift_quadratic m x K hK, gaussianMeanDensityWeight]
    simp only [mul_assoc, ← Real.exp_add]
    congr 3
    ring
  rw [← ENNReal.ofReal_toReal (ENNReal.toReal_pos_iff.mp hs).2.ne,
    ← ENNReal.ofReal_toReal (ENNReal.toReal_pos_iff.mp hp).2.ne,
    ← ENNReal.ofReal_mul hp.le, he]

/-- The actual translated Gaussian law has the exact exponential linear density relative to its center. -/
theorem gaussianMeanCoordinateLaw_changeDensity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℝ) (K : Matrix ι ι ℝ) (hK : K.PosDef) :
    gaussianMeanCoordinateLaw m K = (gaussianCoordinateLaw K).withDensity
      (fun x ↦ ENNReal.ofReal (gaussianMeanDensityWeight m K x)) := by
  rw [gaussianMeanCoordinateLaw_density m K hK]
  unfold gaussianCoordinateLaw
  rw [multivariateGaussian_coordinate_density K hK,
    ← withDensity_mul volume (gaussianCovarianceDensity_measurable K)
      (gaussianMeanDensityWeight_measurable m K).ennreal_ofReal]
  congr 1
  funext x
  exact gaussianMeanCovarianceDensity_mul_weight m K hK x

end SRWTightness
