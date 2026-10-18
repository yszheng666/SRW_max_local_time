import SRWTightness.ReferenceSignedCgfThird
import SRWTightness.CgfTaylorThirdRemainder

open MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace SRWTightness

/-- The actual signed normalized reference mark has a uniform cubic cgf remainder for both tilt signs. -/
theorem referenceMark_signed_cgf_taylor (D K : Finset Site) (hKD : K ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1)
    (w : K → ℝ) (hw1 : ∑ z, |w z| = 1)
    (L : ℝ) (hL : 0 < L) (hαL : α ≤ L)
    (hG : ∀ z : K, killedGreen D z z ≤ L)
    (s : ℝ) (hs : |s| ≤ 1 / (8 * L)) :
    let U := fun Y : Mark K ↦ ∑ z, w z * (Y z : ℝ)
    let μ := referenceMarkLaw D K α
    |cgf U μ s - (∫ Y, U Y ∂μ) * s -
      ((∫ Y, U Y ^ 2 ∂μ) - (∫ Y, U Y ∂μ) ^ 2) * s ^ 2 / 2| ≤
        23592976 * L ^ 3 * |s| ^ 3 / 6 := by
  letI := referenceMarkLaw_isProbabilityMeasure D K α hα hcap
  have hb (v : ℝ) (hv : v ∈ uIcc 0 s) : |v| ≤ 1 / (8 * L) :=
    (by simpa only [sub_zero] using abs_sub_left_of_mem_uIcc hv : |v| ≤ |s|).trans hs
  apply cgf_taylor_third_remainder _ _ _ _ (by positivity)
  · intro v hv
    exact referenceMark_signed_exp_interior D K hKD α hα hcap w hw1 L hL hG v
      ((hb v hv).trans_lt (by apply one_div_lt_one_div_of_lt (by positivity); linarith))
  · intro v hv
    exact referenceMark_signed_cgf_third_bound D K hKD α hα hcap w hw1
      L hL hαL hG v (hb v hv)

end SRWTightness
