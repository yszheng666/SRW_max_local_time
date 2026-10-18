import SRWTightness.GaussianFiniteLawUniqueness

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Measurable real Gaussian paths with matching means and covariances have equal laws. -/
theorem gaussian_process_law_eq_of_mean_covariance {Ω ι : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : ι → Ω → ℝ) (hX : IsGaussianProcess X μ) (hY : IsGaussianProcess Y μ)
    (hx : Measurable (fun ω i ↦ X i ω)) (hy : Measurable (fun ω i ↦ Y i ω))
    (hm : ∀ i, (∫ ω, X i ω ∂μ) = ∫ ω, Y i ω ∂μ)
    (hc : ∀ i j, cov[X i, X j; μ] = cov[Y i, Y j; μ]) :
    μ.map (fun ω i ↦ X i ω) = μ.map (fun ω i ↦ Y i ω) := by
  classical
  apply (map_eq_iff_forall_finset_map_restrict_eq hx.aemeasurable hy.aemeasurable).mpr
  intro I
  exact gaussian_finite_law_eq_of_mean_covariance μ _ _
    (hX.hasGaussianLaw I) (hY.hasGaussianLaw I) (fun i ↦ hm i) (fun i j ↦ hc i j)

end SRWTightness
