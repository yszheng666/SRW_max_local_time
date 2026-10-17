import SRWTightness.TiltedCovarianceDerivative
import SRWTightness.ReferenceTiltedMeanDerivative
import SRWTightness.ReferenceWeightedProductL2

open MeasureTheory ProbabilityTheory
open scoped Topology

namespace SRWTightness

/-- The doubled physical tilt remains in the interior domain needed for weighted differentiation. -/
theorem referenceMark_doubled_exp_interior (D K : Finset Site) (hKD : K ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1)
    (β : K → ℝ) (L : ℝ) (hL : 0 < L) (hG : ∀ z : K, killedGreen D z z ≤ L)
    (s : ℝ) (hs : |s| * (∑ z, |β z|) < 1 / (8 * L)) :
    s ∈ interior (integrableExpSet (fun Y : Mark K ↦ 2 * ∑ z, β z * (Y z : ℝ))
      (referenceMarkLaw D K α)) := by
  have hdouble : |s| * (∑ z, |2 * β z|) < 1 / (4 * L) := by
    have he : (∑ z, |2 * β z|) = 2 * (∑ z, |β z|) := by
      simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), Finset.mul_sum]
    rw [he]
    calc
      _ = 2 * (|s| * ∑ z, |β z|) := by ring
      _ < 2 * (1 / (8 * L)) := mul_lt_mul_of_pos_left hs (by norm_num)
      _ = _ := by ring
  have ht2 := referenceMark_linear_exp_interior D K hKD α hα hcap
    (fun z ↦ 2 * β z) L hL hG s hdouble
  have heX : (fun Y : Mark K ↦ ∑ z, (2 * β z) * (Y z : ℝ)) =
      (fun Y ↦ 2 * ∑ z, β z * (Y z : ℝ)) := by
    funext Y
    simp only [Finset.mul_sum, mul_assoc]
  rwa [heX] at ht2

/-- The covariance response identity for actual probability-weighted mark observations
and every signed physical direction in the strict neighborhood. -/
theorem referenceMark_hasDerivAt_tilted_covariance (D K : Finset Site) (hKD : K ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1)
    (w v : K → ℝ) (hw : ∀ z, 0 ≤ w z) (hv : ∀ z, 0 ≤ v z)
    (hw1 : ∑ z, w z = 1) (hv1 : ∑ z, v z = 1) (β : K → ℝ)
    (L : ℝ) (hL : 0 < L) (hG : ∀ z : K, killedGreen D z z ≤ L)
    (s : ℝ) (hs : |s| * (∑ z, |β z|) < 1 / (8 * L)) :
    let H := fun Y : Mark K ↦ ∑ z, w z * (Y z : ℝ)
    let J := fun Y : Mark K ↦ ∑ z, v z * (Y z : ℝ)
    let X := fun Y : Mark K ↦ ∑ z, β z * (Y z : ℝ)
    let μ := referenceMarkLaw D K α
    let ν := μ.tilted (fun Y ↦ s * X Y)
    HasDerivAt (fun t ↦ covariance H J (μ.tilted (fun Y ↦ t * X Y)))
      (∫ Y, (H Y - ∫ Z, H Z ∂ν) * (J Y - ∫ Z, J Z ∂ν) * (X Y - ∫ Z, X Z ∂ν) ∂ν) s := by
  letI := referenceMarkLaw_isProbabilityMeasure D K α hα hcap
  let μ := referenceMarkLaw D K α
  let H := fun Y : Mark K ↦ ∑ z, w z * (Y z : ℝ)
  let J := fun Y : Mark K ↦ ∑ z, v z * (Y z : ℝ)
  let X := fun Y : Mark K ↦ ∑ z, β z * (Y z : ℝ)
  have hmH : Measurable H := by dsimp [H]; fun_prop
  have hmJ : Measurable J := by dsimp [J]; fun_prop
  have hmX : Measurable X := by dsimp [X]; fun_prop
  have hH0 (Y : Mark K) : 0 ≤ H Y :=
    Finset.sum_nonneg (fun z _ ↦ mul_nonneg (hw z) (Nat.cast_nonneg _))
  have hJ0 (Y : Mark K) : 0 ≤ J Y :=
    Finset.sum_nonneg (fun z _ ↦ mul_nonneg (hv z) (Nat.cast_nonneg _))
  have hH2 : MemLp H 2 μ := memLp_finsetSum Finset.univ
    (fun z _ ↦ (referenceMark_coordinate_memLp_two D K α z).const_mul (w z))
  have hJ2 : MemLp J 2 μ := memLp_finsetSum Finset.univ
    (fun z _ ↦ (referenceMark_coordinate_memLp_two D K α z).const_mul (v z))
  have hHJ2 : MemLp (fun Y ↦ H Y * J Y) 2 μ :=
    referenceMark_weighted_product_memLp_two D K hKD α hα hcap w v hw hv hw1 hv1 L hL hG
  have ht := referenceMark_linear_exp_interior D K hKD α hα hcap β L hL hG s
    (hs.trans (one_div_lt_one_div_of_lt (by positivity) (by linarith)))
  have ht2 := referenceMark_doubled_exp_interior D K hKD α hα hcap β L hL hG s hs
  exact hasDerivAt_tilted_covariance μ H J X hmH hmJ hH0 hJ0 s ht
    (weighted_exponential_interior μ H X hmH hH0 hH2 hmX s ht2)
    (weighted_exponential_interior μ J X hmJ hJ0 hJ2 hmX s ht2)
    (weighted_exponential_interior μ (fun Y ↦ H Y * J Y) X (hmH.mul hmJ)
      (fun Y ↦ mul_nonneg (hH0 Y) (hJ0 Y)) hHJ2 hmX s ht2)

end SRWTightness
