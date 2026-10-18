import SRWTightness.ThirdCgfCenteredMoment
import SRWTightness.ReferenceSignedCenteredMoment

open MeasureTheory ProbabilityTheory
open scoped Topology

namespace SRWTightness

/-- Every strictly small scalar tilt of a signed normalized mark lies inside its exponential domain. -/
theorem referenceMark_signed_exp_interior (D K : Finset Site) (hKD : K ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1)
    (w : K → ℝ) (hw1 : ∑ z, |w z| = 1)
    (L : ℝ) (hL : 0 < L) (hG : ∀ z : K, killedGreen D z z ≤ L)
    (s : ℝ) (hs : |s| < 1 / (4 * L)) :
    s ∈ interior (integrableExpSet (fun Y : Mark K ↦ ∑ z, w z * (Y z : ℝ))
      (referenceMarkLaw D K α)) := by
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (Ioo_mem_nhds (abs_lt.mp hs).1 (abs_lt.mp hs).2)
  intro v hv
  exact (referenceMark_signed_exponential_bound D K hKD α hα hcap w hw1
    L hL hG v (abs_le.mpr ⟨hv.1.le, hv.2.le⟩)).1

/-- A uniform third cgf derivative bound for the actual signed normalized reference mark. -/
theorem referenceMark_signed_cgf_third_bound (D K : Finset Site) (hKD : K ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1)
    (w : K → ℝ) (hw1 : ∑ z, |w z| = 1)
    (L : ℝ) (hL : 0 < L) (hαL : α ≤ L)
    (hG : ∀ z : K, killedGreen D z z ≤ L)
    (s : ℝ) (hs : |s| ≤ 1 / (8 * L)) :
    |iteratedDeriv 3
      (cgf (fun Y : Mark K ↦ ∑ z, w z * (Y z : ℝ)) (referenceMarkLaw D K α)) s| ≤
        23592976 * L ^ 3 := by
  letI := referenceMarkLaw_isProbabilityMeasure D K α hα hcap
  have hcoef : (∑ z, |s * w z|) = |s| := by
    simp only [abs_mul, ← Finset.mul_sum, hw1, mul_one]
  have ht := referenceMark_signed_exp_interior D K hKD α hα hcap w hw1 L hL hG s
    (hs.trans_lt (by apply one_div_lt_one_div_of_lt (by positivity); linarith))
  have hc := referenceMark_tilted_signed_centered_third D K hKD α hα hcap w hw1
    (fun z ↦ s * w z) L hL hαL hG (by rwa [hcoef])
  have he : (fun Y : Mark K ↦ ∑ z, (s * w z) * (Y z : ℝ)) =
      (fun Y : Mark K ↦ s * ∑ z, w z * (Y z : ℝ)) := by
    funext Y
    simp only [Finset.mul_sum, mul_assoc]
  dsimp only at hc
  rw [he] at hc
  rw [iteratedDeriv_three_cgf_eq_centered_moment _ _ _ ht]
  calc
    _ ≤ ∫ Y, |((∑ z, w z * (Y z : ℝ)) - ∫ V, (∑ z, w z * (V z : ℝ))
        ∂(referenceMarkLaw D K α).tilted (fun V ↦ s * ∑ z, w z * (V z : ℝ))) ^ 3|
        ∂(referenceMarkLaw D K α).tilted (fun V ↦ s * ∑ z, w z * (V z : ℝ)) :=
      abs_integral_le_integral_abs
    _ ≤ _ := by simpa only [abs_pow] using hc.2.2

end SRWTightness
