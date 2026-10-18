import SRWTightness.ReferenceWeightedMoments
import Mathlib.MeasureTheory.Measure.Tilted

open MeasureTheory

namespace SRWTightness

/-- Signed normalized coefficients support both signs of a small exponential tilt. -/
theorem referenceMark_signed_exponential_bound (D K : Finset Site) (hKD : K ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1)
    (a : K → ℝ) (ha : ∑ z, |a z| = 1)
    (L : ℝ) (hL : 0 < L) (hG : ∀ z : K, killedGreen D z z ≤ L)
    (s : ℝ) (hsmall : |s| ≤ 1 / (4 * L)) :
    Integrable (fun Y : Mark K ↦ Real.exp (s * ∑ z, a z * (Y z : ℝ)))
      (referenceMarkLaw D K α) ∧
    (∫ Y : Mark K, Real.exp (s * ∑ z, a z * (Y z : ℝ)) ∂referenceMarkLaw D K α) ≤
      1 + 4 * α * |s| := by
  have he := referenceMark_weighted_exponential_bound D K hKD α hα hcap
    (fun z ↦ |a z|) (fun z ↦ abs_nonneg _) ha L hL hG |s| (abs_nonneg s) hsmall
  have hdom (Y : Mark K) : Real.exp (s * ∑ z, a z * (Y z : ℝ)) ≤
      Real.exp (|s| * ∑ z, |a z| * (Y z : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have habs : |∑ z, a z * (Y z : ℝ)| ≤ ∑ z, |a z| * (Y z : ℝ) := by
      have hh := Finset.abs_sum_le_sum_abs (fun z : K ↦ a z * (Y z : ℝ)) Finset.univ
      have hc (z : K) : |(Y z : ℝ)| = (Y z : ℝ) := abs_of_nonneg (Nat.cast_nonneg _)
      simpa only [abs_mul, hc] using hh
    calc
      _ ≤ |s * ∑ z, a z * (Y z : ℝ)| := le_abs_self _
      _ = |s| * |∑ z, a z * (Y z : ℝ)| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left habs (abs_nonneg s)
  have hm : Measurable (fun Y : Mark K ↦ Real.exp (s * ∑ z, a z * (Y z : ℝ))) := by fun_prop
  have hi := he.1.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall (fun Y ↦ by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hdom Y))
  exact ⟨hi, (integral_mono hi he.1 hdom).trans he.2⟩

/-- The normalized actual reference law admits a genuine signed exponential tilt. -/
theorem referenceMark_signed_tilt_probability (D K : Finset Site) (hKD : K ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1)
    (a : K → ℝ) (ha : ∑ z, |a z| = 1)
    (L : ℝ) (hL : 0 < L) (hG : ∀ z : K, killedGreen D z z ≤ L)
    (s : ℝ) (hsmall : |s| ≤ 1 / (4 * L)) :
    IsProbabilityMeasure ((referenceMarkLaw D K α).tilted
      (fun Y : Mark K ↦ s * ∑ z, a z * (Y z : ℝ))) := by
  letI := referenceMarkLaw_isProbabilityMeasure D K α hα hcap
  exact isProbabilityMeasure_tilted
    (referenceMark_signed_exponential_bound D K hKD α hα hcap a ha L hL hG s hsmall).1

end SRWTightness
