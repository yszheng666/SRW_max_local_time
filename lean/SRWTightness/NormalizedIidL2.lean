import SRWTightness.NormalizedProductCovariance

open MeasureTheory

namespace SRWTightness

/-- A square-integrable mark observation yields a square-integrable normalized iid sum. -/
theorem normalizedWeightedSum_memLp_two_iid (K : Finset Site) (k : ℕ) (α g u : ℝ)
    (μ : Measure (Mark K)) [IsProbabilityMeasure μ] (w : K → ℝ)
    (hw : MemLp (fun Y : Mark K ↦ ∑ z, w z * (Y z : ℝ)) 2 μ) :
    MemLp (normalizedWeightedSum K k α g u w) 2 (Measure.pi (fun _ : Fin k ↦ μ)) := by
  have hi : MemLp (fun Y : MarkSamples K k ↦ ∑ i, ∑ z, w z * (Y i z : ℝ)) 2
      (Measure.pi (fun _ : Fin k ↦ μ)) := memLp_finsetSum Finset.univ
    (fun i _ ↦ hw.comp_measurePreserving (measurePreserving_eval (fun _ : Fin k ↦ μ) i))
  have he : normalizedWeightedSum K k α g u w =
      (fun Y ↦ ((∑ i, ∑ z, w z * (Y i z : ℝ)) - α * k * ∑ z, w z) /
        (u * Real.sqrt (α * g))) := funext (normalizedWeightedSum_sum_algebra K k α g u w)
  rw [he]
  simpa only [div_eq_mul_inv, Pi.sub_apply] using
    (hi.sub (memLp_const (α * k * ∑ z, w z))).mul_const (u * Real.sqrt (α * g))⁻¹

end SRWTightness
