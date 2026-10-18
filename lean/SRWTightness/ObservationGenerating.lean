import SRWTightness.GeneratingPoisson
import SRWTightness.ReferenceRestriction

open Matrix MeasureTheory

namespace SRWTightness

 theorem observation_generating_equation (D A : Finset Site) (hAD : A ⊆ D)
    (v : A → ℝ) (hv0 : ∀ z, 0 ≤ v z) (hv1 : ∀ z, v z ≤ 1) :
    (observationResolventMatrix D A v).mulVec
      (fun z : A ↦ afterStepGenerating D A v z) = 1 := by
  let t : A → ℝ := fun z ↦ afterStepGenerating D A v z
  let c : A → ℝ := fun z ↦ (v z - 1) * t z
  have hc : (Matrix.diagonal (fun z ↦ v z - 1)).mulVec t = c := by
    funext z
    exact Matrix.mulVec_diagonal _ _ _
  funext z
  have hg := generating_green_representation D A hAD v hv0 hv1 z
  have hh := killedGenerating_first_step D A v hv0 hv1 z (hAD z.property)
  change killedGenerating D A v z = siteWeight A v z * t z at hh
  simp only [siteWeight, dif_pos z.property] at hh
  change killedGenerating D A v z - 1 = (observationGreen D A).mulVec c z at hg
  change (observationResolventMatrix D A v).mulVec t z = 1
  simp only [observationResolventMatrix, Matrix.sub_mulVec, Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec, Pi.sub_apply]
  rw [hc]
  change t z - ((observationGreen D A).mulVec c z - c z) = 1
  dsimp [c]
  nlinarith

 theorem observation_generating_inverse (D A : Finset Site) (hAD : A ⊆ D)
    (v : A → ℝ) (hv0 : ∀ z, 0 ≤ v z) (hv1 : ∀ z, v z ≤ 1) :
    (fun z : A ↦ afterStepGenerating D A v z) =
      (observationResolventMatrix D A v)⁻¹.mulVec 1 := by
  let B := observationResolventMatrix D A v
  have hB : IsUnit B := observationResolventMatrix_isUnit D A hAD v hv0 hv1
  have he := congrArg (fun f : A → ℝ ↦ B⁻¹.mulVec f)
    (observation_generating_equation D A hAD v hv0 hv1)
  change B⁻¹.mulVec (B.mulVec (fun z : A ↦ afterStepGenerating D A v z)) = _ at he
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul B
    ((Matrix.isUnit_iff_isUnit_det B).mp hB), Matrix.one_mulVec] at he
  exact he

 theorem equilibrium_observationLift (D A : Finset Site) (hAD : A ⊆ D) (c : A → ℝ) :
    (∑ x : A, equilibriumMeasure D A x * observationLift D A c x) = ∑ z : A, c z := by
  unfold observationLift
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  rw [← Finset.sum_mul]
  have he := equilibrium_green_on_set D A hAD z z.property
  rw [← Finset.sum_coe_sort A (fun x ↦ equilibriumMeasure D A x * killedGreen D x z)] at he
  rw [he, one_mul]

/-- The observation-set version of the reference generating function for parameters in [0,1].
Positive exponential parameters require an additional integrability argument. -/
theorem referenceMark_observation_generating (D A : Finset Site) (hAD : A ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D A ≤ 1)
    (v : A → ℝ) (hv0 : ∀ z, 0 ≤ v z) (hv1 : ∀ z, v z ≤ 1) :
    (∫ Y, markMonomial v Y ∂referenceMarkLaw D A α) = 1 + α *
      ∑ z : A, (v z - 1) * ((observationResolventMatrix D A v)⁻¹.mulVec 1) z := by
  rw [integral_reference_centered D A α hα hcap _ (measurable_markMonomial v) 1
    (norm_markMonomial_le_one v hv0 hv1), markMonomial_zero]
  rw [← Finset.sum_coe_sort A (fun x ↦ equilibriumMeasure D A x *
    (markTestExpectation D A (markMonomial v) x - 1))]
  change 1 + α * (∑ x : A, equilibriumMeasure D A x * (killedGenerating D A v x - 1)) = _
  simp_rw [generating_green_representation D A hAD v hv0 hv1]
  rw [equilibrium_observationLift D A hAD]
  have ht := observation_generating_inverse D A hAD v hv0 hv1
  simp_rw [show ∀ z : A, afterStepGenerating D A v z =
    ((observationResolventMatrix D A v)⁻¹.mulVec 1) z from fun z ↦ congrFun ht z]

end SRWTightness
