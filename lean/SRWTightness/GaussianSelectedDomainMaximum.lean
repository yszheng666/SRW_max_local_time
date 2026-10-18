import SRWTightness.GaussianDomainDecomposition
import SRWTightness.IndependentSelectedMaximumComparison

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Domain enlargement retains exactly the selected observation points. -/
theorem gaussian_selected_maximum_domain_comparison (D E : Finset Site)
    (hED : E ⊆ D) (J : Finset E) (t : ℝ) :
    (gaussianGreenLaw E E).real (upperExceedanceOn J t) ≤
      2 * (gaussianGreenLaw D E).real (upperExceedanceOn J t) := by
  have hm := independent_maximum_on_comparison
    (gaussianGreenLaw E E) (harmonicGaussianLaw D E) J
    (fun z ↦ multivariateGaussian_zero_coordinate_nonnegative _
      (green_difference_posSemidef D E hED) z) t
  rw [gaussian_domain_decomposition D E hED] at hm
  exact hm

/-- The selected-domain comparison in the positive normalization used by the source. -/
theorem gaussian_selected_normalized_domain_comparison (D E : Finset Site)
    (hED : E ⊆ D) (J : Finset E) (σ t : ℝ) (hσ : 0 < σ) :
    (gaussianGreenLaw E E).real {φ | ∃ x ∈ J, t ≤ φ x / σ} ≤
      2 * (gaussianGreenLaw D E).real {φ | ∃ x ∈ J, t ≤ φ x / σ} := by
  have he : {φ : EuclideanSpace ℝ E | ∃ x ∈ J, t ≤ φ x / σ} =
      upperExceedanceOn J (t * σ) := by
    ext φ
    simp only [upperExceedanceOn, Set.mem_setOf_eq, le_div_iff₀ hσ]
  rw [he]
  exact gaussian_selected_maximum_domain_comparison D E hED J (t * σ)

end SRWTightness
