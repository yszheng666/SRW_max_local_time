import SRWTightness.WeightedExponentialMoment
import SRWTightness.ReferenceSixthMoment

open MeasureTheory

namespace SRWTightness

/-- Actual reference-mark probability averages have the same quantitative exponential bound. -/
theorem referenceMark_weighted_exponential_bound (D K : Finset Site) (hKD : K ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1)
    (w : K → ℝ) (hw : ∀ z, 0 ≤ w z) (hw1 : ∑ z, w z = 1)
    (L : ℝ) (hL : 0 < L) (hG : ∀ z : K, killedGreen D z z ≤ L)
    (s : ℝ) (hs : 0 ≤ s) (hsmall : s ≤ 1 / (4 * L)) :
    Integrable (fun Y : Mark K ↦ Real.exp (s * ∑ z, w z * (Y z : ℝ)))
      (referenceMarkLaw D K α) ∧
    (∫ Y : Mark K, Real.exp (s * ∑ z, w z * (Y z : ℝ)) ∂referenceMarkLaw D K α) ≤
      1 + 4 * α * s := by
  have he (z : K) := referenceMark_coordinate_exponential_bound D K hKD α hα hcap z s hs
    (hsmall.trans (one_div_le_one_div_of_le
      (by have hh := killedGreen_diag_ge_one D z (hKD z.property); positivity)
      (mul_le_mul_of_nonneg_left (hG z) (by norm_num))))
  exact weighted_exponential_moment (referenceMarkLaw D K α) w hw hw1
    (fun z Y ↦ (Y z : ℝ))
    (fun z ↦ (measurable_of_countable (fun n : ℕ ↦ (n : ℝ))).comp (measurable_pi_apply z))
    s (1 + 4 * α * s) (fun z ↦ (he z).1) (fun z ↦ (he z).2)

/-- A common diagonal Green bound gives a sixth moment independent of the number of sites. -/
theorem referenceMark_weighted_sixth_moment (D K : Finset Site) (hKD : K ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1)
    (w : K → ℝ) (hw : ∀ z, 0 ≤ w z) (hw1 : ∑ z, w z = 1)
    (L : ℝ) (hL : 0 < L) (hG : ∀ z : K, killedGreen D z z ≤ L) :
    Integrable (fun Y : Mark K ↦ (∑ z, w z * (Y z : ℝ)) ^ 6) (referenceMarkLaw D K α) ∧
    (∫ Y : Mark K, (∑ z, w z * (Y z : ℝ)) ^ 6 ∂referenceMarkLaw D K α) ≤
      2949120 * α * L ^ 5 := by
  letI := referenceMarkLaw_isProbabilityMeasure D K α hα hcap
  let s := 1 / (4 * L)
  have hs : 0 < s := by dsimp [s]; positivity
  have he := referenceMark_weighted_exponential_bound D K hKD α hα hcap w hw hw1
    L hL hG s hs.le le_rfl
  have hm : Measurable (fun Y : Mark K ↦ ∑ z, w z * (Y z : ℝ)) := by fun_prop
  have hnonneg (Y : Mark K) : 0 ≤ ∑ z, w z * (Y z : ℝ) :=
    Finset.sum_nonneg (fun z _ ↦ mul_nonneg (hw z) (Nat.cast_nonneg _))
  have hh := sixth_moment_of_exponential (referenceMarkLaw D K α) _ hm hnonneg s
    (4 * α) hs he.1 (by simpa only [mul_assoc] using he.2)
  refine ⟨hh.1, hh.2.trans_eq ?_⟩
  dsimp [s]
  field_simp
  <;> ring

end SRWTightness
