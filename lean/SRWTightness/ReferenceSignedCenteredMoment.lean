import SRWTightness.ReferenceTiltedThirdMoment
import SRWTightness.SignedCenteredThirdMoment

open MeasureTheory

namespace SRWTightness

/-- An arbitrary signed normalized observation has a uniform centered third moment
under every small signed tilt of the actual reference law. -/
theorem referenceMark_tilted_signed_centered_third (D K : Finset Site) (hKD : K ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1)
    (a : K → ℝ) (ha : ∑ z, |a z| = 1)
    (β : K → ℝ) (L : ℝ) (hL : 0 < L) (hαL : α ≤ L)
    (hG : ∀ z : K, killedGreen D z z ≤ L)
    (hsmall : (∑ z, |β z|) ≤ 1 / (8 * L)) :
    let ν := (referenceMarkLaw D K α).tilted (fun Y : Mark K ↦ ∑ z, β z * (Y z : ℝ))
    let U := fun Y : Mark K ↦ ∑ z, a z * (Y z : ℝ)
    Integrable U ν ∧
    Integrable (fun Y ↦ |U Y - ∫ V, U V ∂ν| ^ 3) ν ∧
    (∫ Y, |U Y - ∫ V, U V ∂ν| ^ 3 ∂ν) ≤ 23592976 * L ^ 3 := by
  let ν := (referenceMarkLaw D K α).tilted (fun Y : Mark K ↦ ∑ z, β z * (Y z : ℝ))
  let U := fun Y : Mark K ↦ ∑ z, a z * (Y z : ℝ)
  let W := fun Y : Mark K ↦ ∑ z, |a z| * (Y z : ℝ)
  have hB4 : (∑ z, |β z|) ≤ 1 / (4 * L) := hsmall.trans
    (one_div_le_one_div_of_le (by positivity) (by linarith))
  letI : IsProbabilityMeasure ν :=
    referenceMark_linear_tilt_probability D K hKD α hα hcap β L hL hG hB4
  have hW := referenceMark_tilted_weighted_third_moment D K hKD α hα hcap
    (fun z ↦ |a z|) (fun z ↦ abs_nonneg _) ha β L hL hαL hG hsmall
  have hdom (Y : Mark K) : |U Y| ^ 3 ≤ W Y ^ 3 := by
    apply pow_le_pow_left₀ (abs_nonneg _) _ 3
    have hh := Finset.abs_sum_le_sum_abs (fun z : K ↦ a z * (Y z : ℝ)) Finset.univ
    have hc (z : K) : |(Y z : ℝ)| = (Y z : ℝ) := abs_of_nonneg (Nat.cast_nonneg _)
    simpa only [U, W, abs_mul, hc] using hh
  have hm : Measurable (fun Y ↦ |U Y| ^ 3) := by dsimp [U]; fun_prop
  have hi3 : Integrable (fun Y ↦ |U Y| ^ 3) ν := hW.1.mono'
    hm.aestronglyMeasurable (Filter.Eventually.of_forall (fun Y ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) 3)]
      exact hdom Y))
  have hc := signed_centered_third_moment ν U (by dsimp [U]; fun_prop) hi3
  refine ⟨hc.1, hc.2.1, hc.2.2.trans ?_⟩
  calc
    _ ≤ 8 * (2949122 * L ^ 3) := mul_le_mul_of_nonneg_left
      ((integral_mono hi3 hW.1 hdom).trans hW.2) (by norm_num)
    _ = _ := by ring

end SRWTightness
