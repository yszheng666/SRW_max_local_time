import SRWTightness.GeneratingNeighborhood
import SRWTightness.ReferenceGeneratingIntegrable
import SRWTightness.ReferenceRestrictionLaw

open MeasureTheory Filter
open scoped Topology

namespace SRWTightness

 theorem referenceMark_restriction_integral_measurable (D A K : Finset Site)
    (hAK : A ⊆ K) (hKD : K ⊆ D) (α : ℝ) (hα : 0 ≤ α)
    (hcap : α * capacity D K ≤ 1) (F : Mark A → ℝ) (hF : Measurable F) :
    (∫ Y, F (restrictMark hAK Y) ∂referenceMarkLaw D K α) =
      ∫ Y, F Y ∂referenceMarkLaw D A α := by
  have he := integral_map (μ := referenceMarkLaw D K α)
    (measurable_restrictMark hAK).aemeasurable hF.aestronglyMeasurable
  rw [referenceMark_restriction_law D A K hAK hKD α hα hcap] at he
  exact he.symm

/-- Formula (2.16) for the projected observation vector throughout the unit cube. -/
theorem referenceMark_generating_unit_cube (D A K : Finset Site)
    (hAK : A ⊆ K) (hKD : K ⊆ D) (α : ℝ) (hα : 0 ≤ α)
    (hcap : α * capacity D K ≤ 1) (v : A → ℝ)
    (hv0 : ∀ z, 0 ≤ v z) (hv1 : ∀ z, v z ≤ 1) :
    (∫ Y, markMonomial v (restrictMark hAK Y) ∂referenceMarkLaw D K α) =
      1 + α * ∑ z : A, (v z - 1) * ((observationResolventMatrix D A v)⁻¹.mulVec 1) z := by
  rw [referenceMark_restriction_integral_measurable D A K hAK hKD α hα hcap _
    (measurable_markMonomial v)]
  exact referenceMark_observation_generating D A (hAK.trans hKD) α hα
    ((mul_le_mul_of_nonneg_left (capacity_mono_set D A K hAK hKD) hα).trans hcap) v hv0 hv1

/-- Formula (2.16) on an open neighborhood of the all-one vector, including positive tilts. -/
theorem referenceMark_generating_near_one (D A K : Finset Site)
    (hAK : A ⊆ K) (hKD : K ⊆ D) (α : ℝ) (hα : 0 ≤ α)
    (hcap : α * capacity D K ≤ 1) :
    ∀ᶠ v : A → ℝ in 𝓝 1,
      (∫ Y, markMonomial v (restrictMark hAK Y) ∂referenceMarkLaw D K α) =
        1 + α * ∑ z : A, (v z - 1) * ((observationResolventMatrix D A v)⁻¹.mulVec 1) z := by
  filter_upwards [eventually_integrable_killedMonomial D A (hAK.trans hKD),
    eventually_observationResolvent_isUnit D A] with v hI hB
  rw [referenceMark_restriction_integral_measurable D A K hAK hKD α hα hcap _
    (measurable_markMonomial v)]
  exact referenceMark_observation_generating_integrable D A (hAK.trans hKD) α hα
    ((mul_le_mul_of_nonneg_left (capacity_mono_set D A K hAK hKD) hα).trans hcap) v hI hB

end SRWTightness
