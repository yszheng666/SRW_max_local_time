import SRWTightness.GaussianDomainDecomposition
import SRWTightness.IndependentMaximumComparison

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Domain enlargement costs at most two for a maximum upper event on the original domain. -/
theorem gaussian_maximum_domain_comparison (D E : Finset Site) (hED : E ⊆ D) (t : ℝ) :
    (gaussianGreenLaw E E).real (upperExceedance t) ≤
      2 * (gaussianGreenLaw D E).real (upperExceedance t) := by
  have hm := independent_maximum_comparison (gaussianGreenLaw E E) (harmonicGaussianLaw D E)
    (fun z ↦ multivariateGaussian_zero_coordinate_nonnegative _
      (green_difference_posSemidef D E hED) z) t
  rw [gaussian_domain_decomposition D E hED] at hm
  exact hm

theorem gaussian_observation_maximum_le_domain (D E : Finset Site) (hED : E ⊆ D) (t : ℝ) :
    (gaussianGreenLaw D E).real (upperExceedance t) ≤
      (gaussianGreenLaw D D).real (upperExceedance t) := by
  have hp := gaussianGreenLaw_restrict D E D hED (Finset.Subset.refl D)
  rw [← hp.map_eq, map_measureReal_apply hp.measurable (measurableSet_upperExceedance t)]
  refine measureReal_mono ?_ (measure_ne_top _ _)
  rintro φ ⟨z, hz⟩
  exact ⟨⟨z, hED z.property⟩, hz⟩

/-- The finite-domain comparison underlying enlargement to a dyadic square. -/
theorem gaussian_maximum_le_larger_domain (D E : Finset Site) (hED : E ⊆ D) (t : ℝ) :
    (gaussianGreenLaw E E).real (upperExceedance t) ≤
      2 * (gaussianGreenLaw D D).real (upperExceedance t) :=
  (gaussian_maximum_domain_comparison D E hED t).trans
    (mul_le_mul_of_nonneg_left (gaussian_observation_maximum_le_domain D E hED t) (by norm_num))

end SRWTightness
