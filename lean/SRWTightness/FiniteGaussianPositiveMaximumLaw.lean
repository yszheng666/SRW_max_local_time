import SRWTightness.FiniteGaussianAbsoluteMaximumLaw

open MeasureTheory ProbabilityTheory Set
namespace SRWTightness

/-- The positive part of the normalized, centered maximum on the observation set. -/
noncomputable def finiteGaussianPositiveMaximum {ι : Type*} [Fintype ι]
    (J : Finset ι) (hJ : J.Nonempty) (σ m : ℝ) (φ : EuclideanSpace ℝ ι) : ℝ :=
  max (J.sup' hJ (fun x ↦ φ x / σ) - m) 0

theorem continuous_finiteGaussianPositiveMaximum {ι : Type*} [Fintype ι]
    (J : Finset ι) (hJ : J.Nonempty) (σ m : ℝ) :
    Continuous (finiteGaussianPositiveMaximum J hJ σ m) := by
  have hs : Continuous (fun φ : EuclideanSpace ℝ ι ↦ J.sup' hJ (fun x ↦ φ x / σ)) :=
    Continuous.finset_sup'_apply hJ (fun x _ ↦ by fun_prop)
  exact (hs.sub continuous_const).max continuous_const

noncomputable def finiteGaussianPositiveMaximumLaw {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (J : Finset ι) (hJ : J.Nonempty) (σ m : ℝ) : Measure ℝ :=
  (multivariateGaussian (0 : EuclideanSpace ℝ ι) S).map
    (finiteGaussianPositiveMaximum J hJ σ m)

theorem finiteGaussianPositiveMaximumLaw_isProbabilityMeasure {ι : Type*}
    [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ)
    (J : Finset ι) (hJ : J.Nonempty) (σ m : ℝ) :
    IsProbabilityMeasure (finiteGaussianPositiveMaximumLaw S J hJ σ m) := by
  unfold finiteGaussianPositiveMaximumLaw
  exact Measure.isProbabilityMeasure_map
    (continuous_finiteGaussianPositiveMaximum J hJ σ m).measurable.aemeasurable

theorem finiteGaussianPositiveMaximumLaw_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (J : Finset ι) (hJ : J.Nonempty) (σ m : ℝ) :
    ∀ᵐ u ∂finiteGaussianPositiveMaximumLaw S J hJ σ m, 0 ≤ u := by
  unfold finiteGaussianPositiveMaximumLaw
  apply (ae_map_iff
    (continuous_finiteGaussianPositiveMaximum J hJ σ m).measurable.aemeasurable
    measurableSet_Ici).mpr
  exact Filter.Eventually.of_forall fun φ ↦ le_max_right _ _

/-- At positive heights the centered positive maximum has the original field's tail event. -/
theorem finiteGaussianPositiveMaximumLaw_tail {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (J : Finset ι) (hJ : J.Nonempty) (σ m u : ℝ) (hu : 0 < u) :
    (finiteGaussianPositiveMaximumLaw S J hJ σ m).real (Ici u) =
      (multivariateGaussian (0 : EuclideanSpace ℝ ι) S).real
        {φ | ∃ x ∈ J, m + u ≤ φ x / σ} := by
  rw [finiteGaussianPositiveMaximumLaw, map_measureReal_apply
    (continuous_finiteGaussianPositiveMaximum J hJ σ m).measurable measurableSet_Ici]
  congr 1
  ext φ
  change u ≤ max (J.sup' hJ (fun x ↦ φ x / σ) - m) 0 ↔ _
  rw [le_max_iff, or_iff_left (not_le.mpr hu)]
  have he : u ≤ J.sup' hJ (fun x ↦ φ x / σ) - m ↔
      m + u ≤ J.sup' hJ (fun x ↦ φ x / σ) := by
    constructor <;> intro h <;> linarith
  rw [he]
  exact Finset.le_sup'_iff hJ

end SRWTightness
