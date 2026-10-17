import SRWTightness.ReferenceIntegral
import SRWTightness.SecondMomentFormula
import SRWTightness.GreenSymmetry
import Mathlib.Probability.Moments.Covariance

open MeasureTheory ProbabilityTheory

namespace SRWTightness

 theorem integrable_killedMark_product (D K : Finset Site) (x : Site) (y z : K) :
    Integrable (fun Y : Mark K ↦ (Y y : ℝ) * Y z) (killedMarkLaw D K x) := by
  have hm : Measurable (fun Y : Mark K ↦ (Y y : ℝ) * Y z) :=
    ((measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp (measurable_pi_apply y)).mul
      ((measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp (measurable_pi_apply z))
  exact (integrable_map_measure hm.aestronglyMeasurable
    (measurable_killedMark D K x).aemeasurable).mpr (integrable_domainLocalTime_mul D x y z)

 theorem integral_killedMark_product (D K : Finset Site) (x : Site) (y z : K) :
    ∫ Y, (Y y : ℝ) * Y z ∂killedMarkLaw D K x = occupationSecondMoment D x y z := by
  have hm : Measurable (fun Y : Mark K ↦ (Y y : ℝ) * Y z) :=
    ((measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp (measurable_pi_apply y)).mul
      ((measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp (measurable_pi_apply z))
  exact integral_map (measurable_killedMark D K x).aemeasurable hm.aestronglyMeasurable

 theorem referenceMark_second_moment (D K : Finset Site) (hKD : K ⊆ D) (α : ℝ)
    (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1) (y z : K) :
    ∫ Y, (Y y : ℝ) * Y z ∂referenceMarkLaw D K α =
      2 * α * killedGreen D y z - α * (if y = z then 1 else 0) := by
  rw [integral_referenceMark D K α hα hcap _
    (fun x _ ↦ integrable_killedMark_product D K x y z)]
  simp only [Pi.zero_apply, Nat.cast_zero, mul_zero, zero_add, integral_killedMark_product]
  simp_rw [occupationSecondMoment_formula D _ y z (hKD y.property) (hKD z.property)]
  have he : (∑ x ∈ K, (α * equilibriumMeasure D K x) *
      (killedGreen D x y * killedGreen D y z + killedGreen D x z * killedGreen D z y -
        (if (y : Site) = (z : Site) then killedGreen D x y else 0))) =
      α * killedGreen D y z * (∑ x ∈ K, equilibriumMeasure D K x * killedGreen D x y) +
      α * killedGreen D z y * (∑ x ∈ K, equilibriumMeasure D K x * killedGreen D x z) -
      (if y = z then α * (∑ x ∈ K, equilibriumMeasure D K x * killedGreen D x y) else 0) := by
    by_cases hyz : y = z
    · subst z
      simp only [if_pos rfl, ite_true]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    · have hv : (y : Site) ≠ (z : Site) := fun h ↦ hyz (Subtype.ext h)
      simp only [if_neg hyz, if_neg hv, sub_zero]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      ring
  rw [he, equilibrium_green_on_set D K hKD y y.property,
    equilibrium_green_on_set D K hKD z z.property,
    killedGreen_symm D z y (hKD z.property) (hKD y.property)]
  by_cases h : y = z <;> simp [h] <;> ring

 theorem referenceMark_coordinate_memLp_two (D K : Finset Site) (α : ℝ) (z : K) :
    MemLp (fun Y : Mark K ↦ (Y z : ℝ)) 2 (referenceMarkLaw D K α) := by
  have hm : Measurable (fun Y : Mark K ↦ (Y z : ℝ)) :=
    (measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp (measurable_pi_apply z)
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  simpa only [pow_two] using integrable_referenceMark D K α _
    (fun x _ ↦ integrable_killedMark_product D K x z z)

/-- Manuscript (2.17): both the diagonal discrete-time and rank-one mean corrections. -/
theorem referenceMark_covariance (D K : Finset Site) (hKD : K ⊆ D) (α : ℝ)
    (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1) (y z : K) :
    covariance (fun Y : Mark K ↦ (Y y : ℝ)) (fun Y : Mark K ↦ (Y z : ℝ))
      (referenceMarkLaw D K α) =
      2 * α * killedGreen D y z - α * (if y = z then 1 else 0) - α ^ 2 := by
  letI := referenceMarkLaw_isProbabilityMeasure D K α hα hcap
  rw [covariance_eq_sub (referenceMark_coordinate_memLp_two D K α y)
    (referenceMark_coordinate_memLp_two D K α z)]
  change (∫ Y, (Y y : ℝ) * Y z ∂referenceMarkLaw D K α) -
    (∫ Y, (Y y : ℝ) ∂referenceMarkLaw D K α) *
      (∫ Y, (Y z : ℝ) ∂referenceMarkLaw D K α) = _
  rw [referenceMark_second_moment D K hKD α hα hcap y z,
    referenceMark_mean D K hKD α hα hcap y, referenceMark_mean D K hKD α hα hcap z,
    pow_two]

end SRWTightness
