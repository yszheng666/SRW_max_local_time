import SRWTightness.ReferenceTiltNormalizer
import SRWTightness.TiltedThirdMoment

open MeasureTheory

namespace SRWTightness

/-- Actual probability-weighted mark observations have uniformly bounded third moments
under every signed tilt in the explicit neighborhood. -/
theorem referenceMark_tilted_weighted_third_moment (D K : Finset Site) (hKD : K ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1)
    (w : K → ℝ) (hw : ∀ z, 0 ≤ w z) (hw1 : ∑ z, w z = 1)
    (β : K → ℝ) (L : ℝ) (hL : 0 < L) (hαL : α ≤ L)
    (hG : ∀ z : K, killedGreen D z z ≤ L)
    (hsmall : (∑ z, |β z|) ≤ 1 / (8 * L)) :
    let ν := (referenceMarkLaw D K α).tilted (fun Y : Mark K ↦ ∑ z, β z * (Y z : ℝ))
    Integrable (fun Y : Mark K ↦ (∑ z, w z * (Y z : ℝ)) ^ 3) ν ∧
    (∫ Y : Mark K, (∑ z, w z * (Y z : ℝ)) ^ 3 ∂ν) ≤ 2949122 * L ^ 3 := by
  letI := referenceMarkLaw_isProbabilityMeasure D K α hα hcap
  have h6 := referenceMark_weighted_sixth_moment D K hKD α hα hcap w hw hw1 L hL hG
  have hb6 : (∫ Y : Mark K, (∑ z, w z * (Y z : ℝ)) ^ 6 ∂referenceMarkLaw D K α) ≤
      2949120 * L ^ 6 := by
    calc
      _ ≤ 2949120 * α * L ^ 5 := h6.2
      _ ≤ 2949120 * L * L ^ 5 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hαL (by norm_num)) (by positivity)
      _ = _ := by ring
  have hB8 := (le_div_iff₀ (by positivity : 0 < 8 * L)).mp hsmall
  have hB4 : (∑ z, |β z|) ≤ 1 / (4 * L) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have hB0 : 0 ≤ ∑ z, |β z| := Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
    nlinarith
  have he := referenceMark_linear_exponential_bound D K hKD α hα hcap β L hL hG hB4
  have hz := referenceMark_tilt_normalizer_lower D K hKD α hα hcap β L hL hαL hG hsmall
  have h2 := referenceMark_double_tilt_bound D K hKD α hα hcap β L hL hαL hG hsmall
  have hh := tilted_third_moment_bound (referenceMarkLaw D K α)
    (fun Y : Mark K ↦ ∑ z, w z * (Y z : ℝ))
    (fun Y : Mark K ↦ ∑ z, β z * (Y z : ℝ)) (by fun_prop) (by fun_prop)
    (fun Y ↦ Finset.sum_nonneg (fun z _ ↦ mul_nonneg (hw z) (Nat.cast_nonneg _)))
    L 2949120 hL h6.1 hb6 he.1 (by linarith) h2.1 h2.2
  norm_num only [show (2949120 : ℝ) + 2 = 2949122 by norm_num] at hh
  exact hh

end SRWTightness
