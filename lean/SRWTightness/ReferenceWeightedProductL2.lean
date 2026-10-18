import SRWTightness.ReferenceWeightedMoments
import SRWTightness.ThirdProductMoment

open MeasureTheory

namespace SRWTightness

/-- Products of actual probability-weighted mark observations are square integrable. -/
theorem referenceMark_weighted_product_memLp_two (D K : Finset Site) (hKD : K ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1)
    (w v : K → ℝ) (hw : ∀ z, 0 ≤ w z) (hv : ∀ z, 0 ≤ v z)
    (hw1 : ∑ z, w z = 1) (hv1 : ∑ z, v z = 1)
    (L : ℝ) (hL : 0 < L) (hG : ∀ z : K, killedGreen D z z ≤ L) :
    MemLp (fun Y : Mark K ↦ (∑ z, w z * (Y z : ℝ)) * (∑ z, v z * (Y z : ℝ))) 2
      (referenceMarkLaw D K α) := by
  letI := referenceMarkLaw_isProbabilityMeasure D K α hα hcap
  let H := fun Y : Mark K ↦ ∑ z, w z * (Y z : ℝ)
  let J := fun Y : Mark K ↦ ∑ z, v z * (Y z : ℝ)
  have h6H := (referenceMark_weighted_sixth_moment D K hKD α hα hcap w hw hw1 L hL hG).1
  have h6J := (referenceMark_weighted_sixth_moment D K hKD α hα hcap v hv hv1 L hL hG).1
  have hdom (Y : Mark K) : (H Y * J Y) ^ 2 ≤ H Y ^ 6 + J Y ^ 6 + 1 := by
    have hh := abs_triple_mul_le_cubes (H Y ^ 2) (J Y ^ 2) 1
    have hleft : |H Y ^ 2 * J Y ^ 2| = H Y ^ 2 * J Y ^ 2 :=
      abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    simp only [mul_one, hleft, abs_of_nonneg (sq_nonneg (H Y)),
      abs_of_nonneg (sq_nonneg (J Y)), abs_one, one_pow] at hh
    nlinarith only [hh]
  have hiB : Integrable (fun Y ↦ H Y ^ 6 + J Y ^ 6 + 1) (referenceMarkLaw D K α) :=
    (h6H.add h6J).add (integrable_const 1)
  have hm : Measurable (fun Y ↦ H Y * J Y) := by dsimp [H, J]; fun_prop
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  have hm2 : Measurable (fun Y ↦ (H Y * J Y) ^ 2) := by fun_prop
  exact hiB.mono' hm2.aestronglyMeasurable (Filter.Eventually.of_forall (fun Y ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hdom Y))

end SRWTightness
