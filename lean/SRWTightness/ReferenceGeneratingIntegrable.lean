import SRWTightness.ObservationIntegrable

open MeasureTheory

namespace SRWTightness
 theorem integral_reference_centered_integrable (D K : Finset Site) (α : ℝ) (hα : 0 ≤ α)
    (hcap : α * capacity D K ≤ 1) (F : Mark K → ℝ) (hF : Measurable F)
    (hI : ∀ x : Site, Integrable (fun ω ↦ F (killedMark D K x ω)) pathLaw) :
    ∫ Y, F Y ∂referenceMarkLaw D K α = F 0 + α *
      ∑ x ∈ K, equilibriumMeasure D K x * (markTestExpectation D K F x - F 0) := by
  rw [integral_referenceMark D K α hα hcap F
    (fun x _ ↦ (integrable_map_measure hF.aestronglyMeasurable
      (measurable_killedMark D K x).aemeasurable).mpr (hI x))]
  have hi (x : Site) : (∫ Y, F Y ∂killedMarkLaw D K x) = markTestExpectation D K F x :=
    integral_map (measurable_killedMark D K x).aemeasurable hF.aestronglyMeasurable
  simp_rw [hi, mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul]
  change (1 - α * capacity D K) * F 0 +
    (∑ x ∈ K, α * equilibriumMeasure D K x * markTestExpectation D K F x) =
    F 0 + α * ((∑ x ∈ K, equilibriumMeasure D K x * markTestExpectation D K F x) - capacity D K * F 0)
  have he : (∑ x ∈ K, α * equilibriumMeasure D K x * markTestExpectation D K F x) =
      α * ∑ x ∈ K, equilibriumMeasure D K x * markTestExpectation D K F x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [he]
  ring

theorem referenceMark_observation_generating_integrable (D A : Finset Site) (hAD : A ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D A ≤ 1)
    (v : A → ℝ) (hI : ∀ x : Site, Integrable (fun ω ↦ markMonomial v (killedMark D A x ω)) pathLaw)
    (hBunit : IsUnit (observationResolventMatrix D A v)) :
    (∫ Y, markMonomial v Y ∂referenceMarkLaw D A α) = 1 + α *
      ∑ z : A, (v z - 1) * ((observationResolventMatrix D A v)⁻¹.mulVec 1) z := by
  rw [integral_reference_centered_integrable D A α hα hcap _ (measurable_markMonomial v) hI, markMonomial_zero]
  rw [← Finset.sum_coe_sort A (fun x ↦ equilibriumMeasure D A x *
    (markTestExpectation D A (markMonomial v) x - 1))]
  change 1 + α * (∑ x : A, equilibriumMeasure D A x * (killedGenerating D A v x - 1)) = _
  simp_rw [generating_green_representation_integrable D A hAD v hI]
  rw [equilibrium_observationLift D A hAD]
  have ht := observation_generating_inverse_integrable D A hAD v hI hBunit
  simp_rw [show ∀ z : A, afterStepGenerating D A v z =
    ((observationResolventMatrix D A v)⁻¹.mulVec 1) z from fun z ↦ congrFun ht z]

end SRWTightness
