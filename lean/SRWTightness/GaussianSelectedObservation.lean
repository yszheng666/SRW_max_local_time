import SRWTightness.GaussianField
import SRWTightness.IndependentSelectedMaximumComparison

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- Restriction preserves the upper event on exactly the selected observations. -/
theorem gaussian_selected_observation_probability (D A K : Finset Site)
    (hAK : A ⊆ K) (hKD : K ⊆ D) (J : Finset A) (t : ℝ) :
    (gaussianGreenLaw D A).real (upperExceedanceOn J t) =
      (gaussianGreenLaw D K).real
        {φ | ∃ x ∈ J, t ≤ φ ⟨x.val, hAK x.property⟩} := by
  have hp := gaussianGreenLaw_restrict D A K hAK hKD
  rw [← hp.map_eq, map_measureReal_apply hp.measurable
    (measurableSet_upperExceedanceOn J t)]
  rfl

end SRWTightness
