import SRWTightness.ProductCovariance
import SRWTightness.ReferenceTiltedWeightedL2
import SRWTightness.ReferenceTiltedCovarianceDrift
import SRWTightness.ReferenceProductTilt

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Covariance drift of actual independent mark sums under a signed physical tilt. -/
theorem referenceMark_product_covariance_drift (D K : Finset Site) (hKD : K ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1)
    (w v : K → ℝ) (hw : ∀ z, 0 ≤ w z) (hv : ∀ z, 0 ≤ v z)
    (hw1 : ∑ z, w z = 1) (hv1 : ∑ z, v z = 1) (β : K → ℝ)
    (L : ℝ) (hL : 0 < L) (hαL : α ≤ L) (hG : ∀ z : K, killedGreen D z z ≤ L)
    (hsmall : (∑ z, |β z|) < 1 / (8 * L)) (k : ℕ) :
    let H := fun Y : MarkSamples K k ↦ ∑ i, ∑ z, w z * (Y i z : ℝ)
    let J := fun Y : MarkSamples K k ↦ ∑ i, ∑ z, v z * (Y i z : ℝ)
    let X := fun Y : MarkSamples K k ↦ ∑ i, ∑ z, β z * (Y i z : ℝ)
    let μ := markProductLaw D K α k
    |covariance H J (μ.tilted X) - covariance H J μ| ≤
      k * (35389464 * L ^ 3 * (∑ z, |β z|)) := by
  letI := referenceMarkLaw_isProbabilityMeasure D K α hα hcap
  let μ := referenceMarkLaw D K α
  let H := fun Y : Mark K ↦ ∑ z, w z * (Y z : ℝ)
  let J := fun Y : Mark K ↦ ∑ z, v z * (Y z : ℝ)
  let X := fun Y : Mark K ↦ ∑ z, β z * (Y z : ℝ)
  have hmH : Measurable H := by dsimp [H]; fun_prop
  have hmJ : Measurable J := by dsimp [J]; fun_prop
  have hs : |(1 : ℝ)| * (∑ z, |β z|) < 1 / (8 * L) := by simpa using hsmall
  have hs4 : (∑ z, |β z|) ≤ 1 / (4 * L) :=
    (hsmall.trans (one_div_lt_one_div_of_lt (by positivity) (by linarith))).le
  have hi := (referenceMark_linear_exponential_bound D K hKD α hα hcap β L hL hG hs4).1
  letI : IsProbabilityMeasure (μ.tilted X) := isProbabilityMeasure_tilted hi
  have htH : MemLp H 2 (μ.tilted X) := by
    simpa only [one_mul] using
      referenceMark_tilted_weighted_memLp_two D K hKD α hα hcap w hw hw1 β L hL hG 1 hs
  have htJ : MemLp J 2 (μ.tilted X) := by
    simpa only [one_mul] using
      referenceMark_tilted_weighted_memLp_two D K hKD α hα hcap v hv hv1 β L hL hG 1 hs
  have hH : MemLp H 2 μ := memLp_finsetSum Finset.univ
    (fun z _ ↦ (referenceMark_coordinate_memLp_two D K α z).const_mul (w z))
  have hJ : MemLp J 2 μ := memLp_finsetSum Finset.univ
    (fun z _ ↦ (referenceMark_coordinate_memLp_two D K α z).const_mul (v z))
  have he := (referenceMark_product_tilt D K hKD α hα hcap β L hL hG hs4 k).2.1
  dsimp only
  rw [he]
  change |covariance (fun Y : Fin k → Mark K ↦ ∑ i, H (Y i))
      (fun Y ↦ ∑ i, J (Y i)) (Measure.pi (fun _ : Fin k ↦ μ.tilted X)) -
    covariance (fun Y : Fin k → Mark K ↦ ∑ i, H (Y i))
      (fun Y ↦ ∑ i, J (Y i)) (Measure.pi (fun _ : Fin k ↦ μ))| ≤ _
  rw [covariance_iid_sum _ H J hmH hmJ htH htJ,
    covariance_iid_sum _ H J hmH hmJ hH hJ, ← mul_sub, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg k)]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg k)
  simpa only [one_mul, abs_one, mul_one] using
    referenceMark_tilted_covariance_drift D K hKD α hα hcap w v hw hv hw1 hv1
      β L hL hαL hG 1 hs

end SRWTightness
