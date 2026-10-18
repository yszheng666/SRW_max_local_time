import SRWTightness.FiniteGaussianAbsoluteMaximum
import Mathlib.MeasureTheory.Measure.Real

open MeasureTheory ProbabilityTheory Set
namespace SRWTightness

/-- The real distribution of the actual absolute coordinate maximum. -/
noncomputable def finiteGaussianAbsMaximumLaw {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (J : Finset ι) (hJ : J.Nonempty) : Measure ℝ :=
  (multivariateGaussian (0 : EuclideanSpace ℝ ι) S).map (finiteGaussianAbsMaximum J hJ)

theorem finiteGaussianAbsMaximumLaw_isProbabilityMeasure {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (J : Finset ι) (hJ : J.Nonempty) :
    IsProbabilityMeasure (finiteGaussianAbsMaximumLaw S J hJ) := by
  unfold finiteGaussianAbsMaximumLaw
  exact Measure.isProbabilityMeasure_map
    (continuous_finiteGaussianAbsMaximum J hJ).measurable.aemeasurable

theorem finiteGaussianAbsMaximumLaw_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (J : Finset ι) (hJ : J.Nonempty) :
    ∀ᵐ u ∂finiteGaussianAbsMaximumLaw S J hJ, 0 ≤ u := by
  unfold finiteGaussianAbsMaximumLaw
  apply (ae_map_iff
    (continuous_finiteGaussianAbsMaximum J hJ).measurable.aemeasurable
    measurableSet_Ici).mpr
  exact Filter.Eventually.of_forall (finiteGaussianAbsMaximum_nonneg J hJ)

/-- The law's upper tail is exactly the finite coordinate-union event. -/
theorem finiteGaussianAbsMaximumLaw_tail {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : Matrix ι ι ℝ) (J : Finset ι) (hJ : J.Nonempty) (u : ℝ) :
    (finiteGaussianAbsMaximumLaw S J hJ).real (Ici u) =
      (multivariateGaussian (0 : EuclideanSpace ℝ ι) S).real
        {φ | ∃ x ∈ J, u ≤ |φ x|} := by
  rw [finiteGaussianAbsMaximumLaw, map_measureReal_apply
    (continuous_finiteGaussianAbsMaximum J hJ).measurable measurableSet_Ici]
  congr 1
  ext φ
  exact le_finiteGaussianAbsMaximum_iff J hJ φ u

end SRWTightness
