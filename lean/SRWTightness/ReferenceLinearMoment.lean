import SRWTightness.ReferenceSecondMoment

open MeasureTheory

namespace SRWTightness

 theorem referenceMark_linear_second_moment (D A : Finset Site) (hAD : A ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D A ≤ 1) (u : A → ℝ) :
    (∫ Y : Mark A, (∑ z : A, u z * (Y z : ℝ)) ^ 2 ∂referenceMarkLaw D A α) =
      2 * α * (∑ y : A, ∑ z : A, u y * killedGreen D y z * u z) -
        α * ∑ z : A, (u z) ^ 2 := by
  have hi (y z : A) : Integrable
      (fun Y : Mark A ↦ (u y * (Y y : ℝ)) * (u z * (Y z : ℝ))) (referenceMarkLaw D A α) := by
    have hh := (integrable_referenceMark D A α _
      (fun x _ ↦ integrable_killedMark_product D A x y z)).const_mul (u y * u z)
    exact hh.congr (Filter.Eventually.of_forall (fun Y ↦ by ring))
  have he (y z : A) :
      (∫ Y : Mark A, (u y * (Y y : ℝ)) * (u z * (Y z : ℝ)) ∂referenceMarkLaw D A α) =
      (u y * u z) * (2 * α * killedGreen D y z - α * (if y = z then 1 else 0)) := by
    calc
      _ = ∫ Y : Mark A, (u y * u z) * ((Y y : ℝ) * Y z) ∂referenceMarkLaw D A α := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun Y ↦ by ring)
      _ = _ := by rw [integral_const_mul, referenceMark_second_moment D A hAD α hα hcap]
  have hpoint (Y : Mark A) : (∑ z : A, u z * (Y z : ℝ)) ^ 2 =
      ∑ y : A, ∑ z : A, (u y * (Y y : ℝ)) * (u z * (Y z : ℝ)) := by
    rw [pow_two, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  simp_rw [hpoint]
  rw [integral_finsetSum Finset.univ (fun y _ ↦ integrable_finsetSum _ (fun z _ ↦ hi y z))]
  simp_rw [integral_finsetSum Finset.univ (fun z _ ↦ hi _ z), he]
  have hterm (y z : A) :
      u y * u z * (2 * α * killedGreen D y z - α * (if y = z then 1 else 0)) =
      2 * α * (u y * killedGreen D y z * u z) -
        α * (if y = z then u z * u z else 0) := by
    by_cases hyz : y = z
    · subst z; simp; ring
    · simp [hyz]; ring
  simp_rw [hterm, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp [pow_two]

end SRWTightness
