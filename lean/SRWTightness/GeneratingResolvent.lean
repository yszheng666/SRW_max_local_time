import SRWTightness.GeneratingFunction
import SRWTightness.WeightedResolvent
import SRWTightness.ReferenceRestriction

open Matrix MeasureTheory

namespace SRWTightness

 theorem siteWeight_nonneg (K : Finset Site) (v : K → ℝ) (hv : ∀ z, 0 ≤ v z) (x : Site) :
    0 ≤ siteWeight K v x := by
  unfold siteWeight
  split_ifs with hx
  · exact hv _
  · norm_num

 theorem siteWeight_le_one (K : Finset Site) (v : K → ℝ) (hv : ∀ z, v z ≤ 1) (x : Site) :
    siteWeight K v x ≤ 1 := by
  unfold siteWeight
  split_ifs with hx
  · exact hv _
  · exact le_rfl

 theorem generating_matrix_equation (D K : Finset Site) (v : K → ℝ)
    (hv0 : ∀ z, 0 ≤ v z) (hv1 : ∀ z, v z ≤ 1) :
    (weightedKilledMatrix D (fun x : D ↦ siteWeight K v x)).mulVec
      (fun x : D ↦ killedGenerating D K v x - 1) = (fun x : D ↦ siteWeight K v x - 1) := by
  funext x
  have hf : ∀ y, y ∉ D → killedGenerating D K v y - 1 = 0 := by
    intro y hy
    rw [killedGenerating_eq_one_of_not_mem D K v y hy, sub_self]
  have hp := killedTransition_mulVec D (fun y ↦ killedGenerating D K v y - 1) hf x
  have hc : (∑ _ : Direction, (1 : ℝ)) = 4 := by simp [Direction]
  rw [Finset.sum_sub_distrib, hc] at hp
  have hh := killedGenerating_first_step D K v hv0 hv1 x x.property
  simp only [weightedKilledMatrix, Matrix.sub_mulVec, Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec, Pi.sub_apply, Matrix.mulVec_diagonal]
  rw [hp]
  nlinarith

 theorem generating_resolvent (D K : Finset Site) (v : K → ℝ)
    (hv0 : ∀ z, 0 ≤ v z) (hv1 : ∀ z, v z ≤ 1) :
    (fun x : D ↦ killedGenerating D K v x - 1) =
      (weightedKilledMatrix D (fun x : D ↦ siteWeight K v x))⁻¹.mulVec
        (fun x : D ↦ siteWeight K v x - 1) := by
  let A := weightedKilledMatrix D (fun x : D ↦ siteWeight K v x)
  have hA : IsUnit A := weightedKilledMatrix_isUnit D _
    (fun x ↦ siteWeight_nonneg K v hv0 x) (fun x ↦ siteWeight_le_one K v hv1 x)
  have he := congrArg (fun f : D → ℝ ↦ A⁻¹.mulVec f) (generating_matrix_equation D K v hv0 hv1)
  change A⁻¹.mulVec (A.mulVec (fun x : D ↦ killedGenerating D K v x - 1)) = _ at he
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).mp hA), Matrix.one_mulVec] at he
  exact he

/-- A full-domain resolvent formula in the bounded parameter range. Reducing this to the
observation-set Green matrix and extending to positive exponential tilts are separate steps. -/
theorem referenceMark_generating_resolvent (D K : Finset Site) (hKD : K ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1)
    (v : K → ℝ) (hv0 : ∀ z, 0 ≤ v z) (hv1 : ∀ z, v z ≤ 1) :
    (∫ Y, markMonomial v Y ∂referenceMarkLaw D K α) = 1 + α *
      ∑ x : K, equilibriumMeasure D K x *
        ((weightedKilledMatrix D (fun y : D ↦ siteWeight K v y))⁻¹.mulVec
          (fun y : D ↦ siteWeight K v y - 1)) ⟨x, hKD x.property⟩ := by
  rw [integral_reference_centered D K α hα hcap _ (measurable_markMonomial v) 1
    (norm_markMonomial_le_one v hv0 hv1), markMonomial_zero]
  rw [← Finset.sum_coe_sort K (fun x ↦ equilibriumMeasure D K x *
    (markTestExpectation D K (markMonomial v) x - 1))]
  congr 2
  apply Finset.sum_congr rfl
  intro x hx
  have he := congrFun (generating_resolvent D K v hv0 hv1) (⟨(x : Site), hKD x.property⟩ : D)
  exact congrArg (fun a : ℝ ↦ equilibriumMeasure D K x * a) he

end SRWTightness
