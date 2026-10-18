import SRWTightness.ReferenceTiltedWeightedL2
import SRWTightness.ReferenceTiltedCovarianceDrift

open MeasureTheory ProbabilityTheory
open scoped Topology

namespace SRWTightness

/-- Coordinate observations are square integrable under every allowed physical tilt. -/
theorem referenceMark_tilted_coordinate_memLp_two (D K : Finset Site) (hKD : K ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1) (β : K → ℝ)
    (L : ℝ) (hL : 0 < L) (hG : ∀ z : K, killedGreen D z z ≤ L)
    (s : ℝ) (hs : |s| * (∑ z, |β z|) < 1 / (8 * L)) (z : K) :
    MemLp (fun Y : Mark K ↦ (Y z : ℝ)) 2
      ((referenceMarkLaw D K α).tilted (fun Y ↦ s * ∑ y, β y * (Y y : ℝ))) := by
  have hh := referenceMark_tilted_weighted_memLp_two D K hKD α hα hcap
    (fun y ↦ if y = z then 1 else 0)
    (by intro y; split_ifs <;> norm_num) (by simp) β L hL hG s hs
  simpa using hh

/-- Summing coordinate covariance errors controls covariance with the signed tilt direction. -/
theorem referenceMark_tilted_direction_covariance_drift (D K : Finset Site) (hKD : K ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1)
    (w : K → ℝ) (hw : ∀ z, 0 ≤ w z) (hw1 : ∑ z, w z = 1) (β : K → ℝ)
    (L : ℝ) (hL : 0 < L) (hαL : α ≤ L) (hG : ∀ z : K, killedGreen D z z ≤ L)
    (s : ℝ) (hs : |s| * (∑ z, |β z|) < 1 / (8 * L)) :
    let H := fun Y : Mark K ↦ ∑ z, w z * (Y z : ℝ)
    let X := fun Y : Mark K ↦ ∑ z, β z * (Y z : ℝ)
    let μ := referenceMarkLaw D K α
    |covariance H X (μ.tilted (fun Y ↦ s * X Y)) - covariance H X μ| ≤
      35389464 * L ^ 3 * (∑ z, |β z|) ^ 2 * |s| := by
  letI := referenceMarkLaw_isProbabilityMeasure D K α hα hcap
  let μ := referenceMarkLaw D K α
  let H := fun Y : Mark K ↦ ∑ z, w z * (Y z : ℝ)
  let X := fun Y : Mark K ↦ ∑ z, β z * (Y z : ℝ)
  let ν := μ.tilted (fun Y ↦ s * X Y)
  have ht := referenceMark_linear_exp_interior D K hKD α hα hcap β L hL hG s
    (hs.trans (one_div_lt_one_div_of_lt (by positivity) (by linarith)))
  have hi := interior_subset (s := integrableExpSet X μ) ht
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_tilted hi
  have hH : MemLp H 2 μ := memLp_finsetSum Finset.univ
    (fun z _ ↦ (referenceMark_coordinate_memLp_two D K α z).const_mul (w z))
  have htH : MemLp H 2 ν :=
    referenceMark_tilted_weighted_memLp_two D K hKD α hα hcap w hw hw1 β L hL hG s hs
  have htY (z : K) : MemLp (fun Y : Mark K ↦ (Y z : ℝ)) 2 ν :=
    referenceMark_tilted_coordinate_memLp_two D K hKD α hα hcap β L hL hG s hs z
  have hc (z : K) :
      |covariance H (fun Y : Mark K ↦ (Y z : ℝ)) ν -
        covariance H (fun Y : Mark K ↦ (Y z : ℝ)) μ| ≤
          35389464 * L ^ 3 * (∑ y, |β y|) * |s| := by
    have hh := referenceMark_tilted_covariance_drift D K hKD α hα hcap w
      (fun y ↦ if y = z then 1 else 0) hw
      (by intro y; split_ifs <;> norm_num) hw1 (by simp) β L hL hαL hG s hs
    simpa [H, X, μ, ν] using hh
  change |covariance H (fun Y ↦ ∑ z, β z * (Y z : ℝ)) ν -
    covariance H (fun Y ↦ ∑ z, β z * (Y z : ℝ)) μ| ≤ _
  rw [covariance_fun_sum_right (fun z ↦ (htY z).const_mul (β z)) htH,
    covariance_fun_sum_right
      (fun z ↦ (referenceMark_coordinate_memLp_two D K α z).const_mul (β z)) hH,
    ← Finset.sum_sub_distrib]
  simp only [covariance_const_mul_right, ← mul_sub, abs_mul]
  calc
    _ ≤ ∑ z, |β z * (covariance H (fun Y : Mark K ↦ (Y z : ℝ)) ν -
        covariance H (fun Y : Mark K ↦ (Y z : ℝ)) μ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ z, |β z| * (35389464 * L ^ 3 * (∑ y, |β y|) * |s|) := by
      apply Finset.sum_le_sum
      intro z _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hc z) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

end SRWTightness
