import SRWTightness.ProductCovariance
import SRWTightness.NormalizedWeightedCovariance

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Rewrite the actual weighted normalized occupation as a centered sum of mark observations. -/
theorem normalizedWeightedSum_sum_algebra (K : Finset Site) (k : ℕ) (α g u : ℝ)
    (w : K → ℝ) (Y : MarkSamples K k) :
    normalizedWeightedSum K k α g u w Y =
      ((∑ i, ∑ z, w z * (Y i z : ℝ)) - α * k * ∑ z, w z) /
        (u * Real.sqrt (α * g)) := by
  unfold normalizedWeightedSum normalizedMarkSum
  simp only [← mul_div_assoc, mul_sub, Finset.mul_sum]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_comm]
  congr 1
  simp only [← Finset.sum_mul, ← Finset.mul_sum]
  ring

/-- Centering and normalization of a finite iid sample give the exact covariance scale. -/
theorem normalizedWeightedSum_covariance_iid (K : Finset Site) (k : ℕ) (α g u : ℝ)
    (μ : Measure (Mark K)) [IsProbabilityMeasure μ] (w v : K → ℝ)
    (hw : MemLp (fun Y : Mark K ↦ ∑ z, w z * (Y z : ℝ)) 2 μ)
    (hv : MemLp (fun Y : Mark K ↦ ∑ z, v z * (Y z : ℝ)) 2 μ) :
    covariance (normalizedWeightedSum K k α g u w) (normalizedWeightedSum K k α g u v)
      (Measure.pi (fun _ : Fin k ↦ μ)) =
      k * covariance (fun Y : Mark K ↦ ∑ z, w z * (Y z : ℝ))
        (fun Y : Mark K ↦ ∑ z, v z * (Y z : ℝ)) μ /
          (u * Real.sqrt (α * g)) / (u * Real.sqrt (α * g)) := by
  have hm (a : K → ℝ) : Measurable (fun Y : Mark K ↦ ∑ z, a z * (Y z : ℝ)) := by
    fun_prop
  have hi (a : K → ℝ)
      (ha : MemLp (fun Y : Mark K ↦ ∑ z, a z * (Y z : ℝ)) 2 μ) :
      Integrable (fun Y : MarkSamples K k ↦ ∑ i, ∑ z, a z * (Y i z : ℝ))
        (Measure.pi (fun _ : Fin k ↦ μ)) := by
    apply integrable_finsetSum
    intro i _
    exact (ha.comp_measurePreserving (measurePreserving_eval (fun _ : Fin k ↦ μ) i)).integrable
      (by norm_num)
  have he (a : K → ℝ) : normalizedWeightedSum K k α g u a =
      (fun Y ↦ ((∑ i, ∑ z, a z * (Y i z : ℝ)) - α * k * ∑ z, a z) /
        (u * Real.sqrt (α * g))) := funext (normalizedWeightedSum_sum_algebra K k α g u a)
  rw [he w, he v, covariance_fun_div_left, covariance_fun_div_right,
    covariance_sub_const_left (hi w hw), covariance_sub_const_right (hi v hv),
    covariance_iid_sum μ _ _ (hm w) (hm v) hw hv]

end SRWTightness
