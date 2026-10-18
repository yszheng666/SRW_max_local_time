import SRWTightness.GaussianMeanDensity
import SRWTightness.GaussianDensityEntropy

open MeasureTheory ProbabilityTheory Matrix

namespace SRWTightness

/-- Coordinates of a translated Gaussian are integrable. -/
theorem gaussianMeanCoordinateLaw_coordinate_integrable {ι : Type*}
    [Fintype ι] [DecidableEq ι] (m : ι → ℝ) (K : Matrix ι ι ℝ) (i : ι) :
    Integrable (fun x : ι → ℝ ↦ x i) (gaussianMeanCoordinateLaw m K) := by
  letI := gaussianCoordinateLaw_isProbabilityMeasure K
  unfold gaussianMeanCoordinateLaw
  apply (integrable_map_measure (measurable_pi_apply i).aestronglyMeasurable
    (show AEMeasurable (fun x : ι → ℝ ↦ m + x) (gaussianCoordinateLaw K) by fun_prop)).mpr
  exact (integrable_const (m i)).add
    ((gaussianCoordinateLaw_coordinate_memLp_two K i).integrable (by norm_num))

/-- Linear forms are integrable under the actual Gaussian with mean m. -/
theorem gaussianMeanCoordinateLaw_linear_integrable {ι : Type*}
    [Fintype ι] [DecidableEq ι] (m v : ι → ℝ) (K A : Matrix ι ι ℝ) :
    Integrable (fun x ↦ v ⬝ᵥ (A *ᵥ x)) (gaussianMeanCoordinateLaw m K) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  exact ((gaussianMeanCoordinateLaw_coordinate_integrable m K j).const_mul (A i j)).const_mul (v i)

/-- A linear form has its value at the specified Gaussian mean as expectation. -/
theorem gaussianMeanCoordinateLaw_linear_mean {ι : Type*}
    [Fintype ι] [DecidableEq ι] (m v : ι → ℝ) (K A : Matrix ι ι ℝ) :
    (∫ x, v ⬝ᵥ (A *ᵥ x) ∂gaussianMeanCoordinateLaw m K) = v ⬝ᵥ (A *ᵥ m) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum]
    · simp_rw [integral_const_mul, gaussianMeanCoordinateLaw_mean]
    · intro j _
      exact ((gaussianMeanCoordinateLaw_coordinate_integrable m K j).const_mul (A i j)).const_mul (v i)
  · intro i _
    exact integrable_finsetSum _ (fun j _ ↦
      ((gaussianMeanCoordinateLaw_coordinate_integrable m K j).const_mul (A i j)).const_mul (v i))

/-- The mean-shift density is everywhere positive. -/
theorem gaussianMeanDensityWeight_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℝ) (K : Matrix ι ι ℝ) (x : ι → ℝ) : 0 ≤ gaussianMeanDensityWeight m K x :=
  (Real.exp_pos _).le

/-- The exact logarithm of the mean-shift density. -/
theorem gaussianMeanDensityWeight_log {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℝ) (K : Matrix ι ι ℝ) (x : ι → ℝ) :
    Real.log (gaussianMeanDensityWeight m K x) =
      m ⬝ᵥ (K⁻¹ *ᵥ x) - (m ⬝ᵥ (K⁻¹ *ᵥ m)) / 2 := by
  exact Real.log_exp _

/-- The log density is integrable under the shifted law. -/
theorem gaussianMeanDensityWeight_log_integrable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℝ) (K : Matrix ι ι ℝ) :
    Integrable (fun x ↦ Real.log (gaussianMeanDensityWeight m K x))
      (gaussianMeanCoordinateLaw m K) := by
  letI := gaussianMeanCoordinateLaw_isProbabilityMeasure m K
  simp_rw [gaussianMeanDensityWeight_log]
  exact (gaussianMeanCoordinateLaw_linear_integrable m m K K⁻¹).sub (integrable_const _)

/-- The exact entropy of shifting a nondegenerate Gaussian mean. -/
theorem gaussian_mean_entropy_formula {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℝ) (K : Matrix ι ι ℝ) (hK : K.PosDef) :
    (∫ x, gaussianMeanDensityWeight m K x * Real.log (gaussianMeanDensityWeight m K x)
      ∂gaussianCoordinateLaw K) = (m ⬝ᵥ (K⁻¹ *ᵥ m)) / 2 := by
  letI := gaussianMeanCoordinateLaw_isProbabilityMeasure m K
  have he := integral_nonnegative_density (gaussianCoordinateLaw K)
    (gaussianMeanDensityWeight m K) (gaussianMeanDensityWeight_measurable m K)
    (gaussianMeanDensityWeight_nonneg m K) (fun x ↦ Real.log (gaussianMeanDensityWeight m K x))
  rw [← gaussianMeanCoordinateLaw_changeDensity m K hK] at he
  rw [← he]
  simp_rw [gaussianMeanDensityWeight_log]
  rw [integral_sub (gaussianMeanCoordinateLaw_linear_integrable m m K K⁻¹)
    (integrable_const _), gaussianMeanCoordinateLaw_linear_mean]
  simp only [integral_const, probReal_univ, one_smul]
  ring

end SRWTightness
