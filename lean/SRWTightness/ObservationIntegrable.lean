import SRWTightness.GeneratingIntegrable
import SRWTightness.ObservationGenerating

open Matrix MeasureTheory

namespace SRWTightness
 theorem observation_generating_equation_integrable (D A : Finset Site) (hAD : A ⊆ D)
    (v : A → ℝ) (hI : ∀ y : Site, Integrable (fun ω ↦ markMonomial v (killedMark D A y ω)) pathLaw) :
    (observationResolventMatrix D A v).mulVec
      (fun z : A ↦ afterStepGenerating D A v z) = 1 := by
  let t : A → ℝ := fun z ↦ afterStepGenerating D A v z
  let c : A → ℝ := fun z ↦ (v z - 1) * t z
  have hc : (Matrix.diagonal (fun z ↦ v z - 1)).mulVec t = c := by
    funext z
    exact Matrix.mulVec_diagonal _ _ _
  funext z
  have hg := generating_green_representation_integrable D A hAD v hI z
  have hh := killedGenerating_first_step_integrable D A v hI z (hAD z.property)
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

 theorem observation_generating_inverse_integrable (D A : Finset Site) (hAD : A ⊆ D)
    (v : A → ℝ) (hI : ∀ y : Site, Integrable (fun ω ↦ markMonomial v (killedMark D A y ω)) pathLaw)
    (hBunit : IsUnit (observationResolventMatrix D A v)) :
    (fun z : A ↦ afterStepGenerating D A v z) =
      (observationResolventMatrix D A v)⁻¹.mulVec 1 := by
  let B := observationResolventMatrix D A v
  have hB : IsUnit B := hBunit
  have he := congrArg (fun f : A → ℝ ↦ B⁻¹.mulVec f)
    (observation_generating_equation_integrable D A hAD v hI)
  change B⁻¹.mulVec (B.mulVec (fun z : A ↦ afterStepGenerating D A v z)) = _ at he
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul B
    ((Matrix.isUnit_iff_isUnit_det B).mp hB), Matrix.one_mulVec] at he
  exact he


end SRWTightness
