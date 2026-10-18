import SRWTightness.NormalizedProductMean
import SRWTightness.CenteredVectorMean

open MeasureTheory WithLp

namespace SRWTightness

/-- The sum of centered transformed mark vectors equals the transformed centered observation. -/
theorem normalized_centered_vector_sum {ι : Type*} [Fintype ι]
    (K : Finset Site) (k : ℕ) (α g u : ℝ)
    (μ : Measure (Mark K)) [IsProbabilityMeasure μ] (w : ι → K → ℝ)
    (hw : ∀ i, MemLp (fun Y : Mark K ↦ ∑ z, w i z * (Y z : ℝ)) 2 μ)
    (T : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) (Y : MarkSamples K k) :
    let c := u * Real.sqrt (α * g)
    let U := fun i (Z : Mark K) ↦ ∑ z, w i z * (Z z : ℝ)
    let V : Mark K → EuclideanSpace ℝ ι := fun Z ↦ toLp 2 (fun i ↦ U i Z - ∫ Z, U i Z ∂μ)
    let F := fun i ↦ normalizedWeightedSum K k α g u (w i)
    let ν := Measure.pi (fun _ : Fin k ↦ μ)
    (∑ j : Fin k, c⁻¹ • T (V (Y j))) =
      T (toLp 2 (fun i ↦ F i Y - ∫ Z, F i Z ∂ν)) := by
  let c := u * Real.sqrt (α * g)
  let U := fun i (Z : Mark K) ↦ ∑ z, w i z * (Z z : ℝ)
  let V : Mark K → EuclideanSpace ℝ ι := fun Z ↦ toLp 2 (fun i ↦ U i Z - ∫ Z, U i Z ∂μ)
  let F := fun i ↦ normalizedWeightedSum K k α g u (w i)
  let ν := Measure.pi (fun _ : Fin k ↦ μ)
  have he : (∑ j : Fin k, c⁻¹ • V (Y j)) =
      toLp 2 (fun i ↦ F i Y - ∫ Z, F i Z ∂ν) := by
    ext i
    change (ofLp (∑ j : Fin k, c⁻¹ • V (Y j))) i = F i Y - ∫ Z, F i Z ∂ν
    simp only [ofLp_sum, ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    change (∑ j : Fin k, c⁻¹ * (U i (Y j) - ∫ Z, U i Z ∂μ)) = _
    rw [show (∫ Z, F i Z ∂ν) = k * ((∫ Z, U i Z ∂μ) - α * ∑ z, w i z) / c from
      normalizedWeightedSum_mean_iid K k α g u μ (w i) (hw i)]
    rw [show F i Y = ((∑ j, U i (Y j)) - α * k * ∑ z, w i z) / c from
      normalizedWeightedSum_sum_algebra K k α g u (w i) Y]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  change (∑ j : Fin k, c⁻¹ • T (V (Y j))) = _
  rw [← he]
  simp only [map_sum, map_smul]

end SRWTightness
