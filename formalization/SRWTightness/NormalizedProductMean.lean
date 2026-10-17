import SRWTightness.NormalizedProductCovariance
import SRWTightness.ReferenceProductCgfTaylor

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- Exact mean of the manuscript's normalized weighted sum under any iid mark law. -/
theorem normalizedWeightedSum_mean_iid (K : Finset Site) (k : ℕ) (α g u : ℝ)
    (μ : Measure (Mark K)) [IsProbabilityMeasure μ] (w : K → ℝ)
    (hw : MemLp (fun Y : Mark K ↦ ∑ z, w z * (Y z : ℝ)) 2 μ) :
    (∫ Y, normalizedWeightedSum K k α g u w Y ∂Measure.pi (fun _ : Fin k ↦ μ)) =
      k * ((∫ Y, (∑ z, w z * (Y z : ℝ)) ∂μ) - α * ∑ z, w z) /
        (u * Real.sqrt (α * g)) := by
  let H := fun Y : Mark K ↦ ∑ z, w z * (Y z : ℝ)
  have hm : Measurable H := by dsimp [H]; fun_prop
  have hi (i : Fin k) : Integrable (fun Y : MarkSamples K k ↦ H (Y i))
      (Measure.pi (fun _ : Fin k ↦ μ)) :=
    (hw.comp_measurePreserving (measurePreserving_eval (fun _ : Fin k ↦ μ) i)).integrable
      (by norm_num)
  have he (i : Fin k) :
      (∫ Y : MarkSamples K k, H (Y i) ∂Measure.pi (fun _ : Fin k ↦ μ)) = ∫ Y, H Y ∂μ := by
    have hh := integral_map (μ := Measure.pi (fun _ : Fin k ↦ μ))
      (measurable_pi_apply i).aemeasurable hm.aestronglyMeasurable
    rw [(measurePreserving_eval (fun _ : Fin k ↦ μ) i).map_eq] at hh
    exact hh.symm
  simp_rw [normalizedWeightedSum_sum_algebra]
  rw [integral_div, integral_sub (integrable_finsetSum _ (fun i _ ↦ hi i)) (integrable_const _),
    integral_finsetSum _ (fun i _ ↦ hi i)]
  simp_rw [he]
  simp [H] <;> ring

/-- Actual normalized reference-mark observations have zero mean before tilting. -/
theorem normalizedWeightedSum_mean_zero (D K : Finset Site) (hKD : K ⊆ D)
    (α g u : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1) (k : ℕ) (w : K → ℝ) :
    (∫ Y, normalizedWeightedSum K k α g u w Y ∂markProductLaw D K α k) = 0 := by
  letI := referenceMarkLaw_isProbabilityMeasure D K α hα hcap
  have hw : MemLp (fun Y : Mark K ↦ ∑ z, w z * (Y z : ℝ)) 2
      (referenceMarkLaw D K α) := memLp_finsetSum Finset.univ
    (fun z _ ↦ (referenceMark_coordinate_memLp_two D K α z).const_mul (w z))
  unfold markProductLaw
  rw [normalizedWeightedSum_mean_iid K k α g u _ w hw,
    referenceMark_linear_mean D K hKD α hα hcap w]
  simp

end SRWTightness
