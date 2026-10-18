import SRWTightness.GaussianDensityRatio

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SRWTightness

noncomputable def gaussianCoordinateLaw {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) : Measure (ι → ℝ) :=
  (multivariateGaussian 0 G).map (fun φ : EuclideanSpace ℝ ι ↦ fun i ↦ φ i)

noncomputable def gaussianDensityWeight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K S : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  (Real.sqrt K.det / Real.sqrt S.det) *
    Real.exp (-(x ⬝ᵥ ((S⁻¹ - K⁻¹) *ᵥ x)) / 2)

theorem gaussianDensityWeight_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K S : Matrix ι ι ℝ) (x : ι → ℝ) : 0 ≤ gaussianDensityWeight K S x := by
  unfold gaussianDensityWeight
  positivity

theorem gaussianDensityWeight_measurable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K S : Matrix ι ι ℝ) : Measurable (gaussianDensityWeight K S) := by
  unfold gaussianDensityWeight
  simp only [dotProduct, Matrix.mulVec]
  fun_prop

theorem gaussianCovarianceDensity_measurable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) : Measurable (gaussianCovarianceDensity G) := by
  unfold gaussianCovarianceDensity
  apply Measurable.mul measurable_const
  apply Finset.measurable_prod
  intro i _
  exact (measurable_gaussianPDF 0 1).comp (by fun_prop)

theorem gaussianDensityWeight_eq_ratio {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K S : Matrix ι ι ℝ) (hK : K.PosDef) (hS : S.PosDef) (x : ι → ℝ) :
    gaussianDensityWeight K S x =
      (gaussianCovarianceDensity S x).toReal / (gaussianCovarianceDensity K x).toReal :=
  (gaussianCovarianceDensity_ratio K S hK hS x).symm

theorem gaussianCovarianceDensity_mul_weight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K S : Matrix ι ι ℝ) (hK : K.PosDef) (hS : S.PosDef) (x : ι → ℝ) :
    gaussianCovarianceDensity S x = gaussianCovarianceDensity K x *
      ENNReal.ofReal (gaussianDensityWeight K S x) := by
  have hp := gaussianCovarianceDensity_toReal_pos K hK x
  have hs := gaussianCovarianceDensity_toReal_pos S hS x
  have hr := gaussianDensityWeight_eq_ratio K S hK hS x
  have hh : (gaussianCovarianceDensity S x).toReal =
      (gaussianCovarianceDensity K x).toReal * gaussianDensityWeight K S x := by
    rw [hr]
    field_simp
  rw [← ENNReal.ofReal_toReal (ENNReal.toReal_pos_iff.mp hs).2.ne,
    ← ENNReal.ofReal_toReal (ENNReal.toReal_pos_iff.mp hp).2.ne,
    ← ENNReal.ofReal_mul hp.le, hh]

theorem gaussianCoordinateLaw_changeDensity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K S : Matrix ι ι ℝ) (hK : K.PosDef) (hS : S.PosDef) :
    gaussianCoordinateLaw S = (gaussianCoordinateLaw K).withDensity
      (fun x ↦ ENNReal.ofReal (gaussianDensityWeight K S x)) := by
  unfold gaussianCoordinateLaw
  rw [multivariateGaussian_coordinate_density S hS, multivariateGaussian_coordinate_density K hK,
    ← withDensity_mul volume (gaussianCovarianceDensity_measurable K)
      (gaussianDensityWeight_measurable K S).ennreal_ofReal]
  congr 1
  funext x
  exact gaussianCovarianceDensity_mul_weight K S hK hS x

theorem gaussianCoordinateLaw_event_integral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K S : Matrix ι ι ℝ) (hK : K.PosDef) (hS : S.PosDef)
    (s : Set (ι → ℝ)) (hs : MeasurableSet s) :
    (gaussianCoordinateLaw S).real s =
      ∫ x in s, gaussianDensityWeight K S x ∂gaussianCoordinateLaw K := by
  rw [gaussianCoordinateLaw_changeDensity K S hK hS]
  have hh := setIntegral_withDensity_eq_setIntegral_toReal_smul
    (μ := gaussianCoordinateLaw K) (gaussianDensityWeight_measurable K S).ennreal_ofReal
    (Filter.Eventually.of_forall (fun x ↦ ENNReal.ofReal_lt_top)) (fun _ ↦ (1 : ℝ)) hs
  simpa only [integral_const, smul_eq_mul, mul_one, Measure.real, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, ENNReal.toReal_ofReal (gaussianDensityWeight_nonneg K S _)] using hh

end SRWTightness
