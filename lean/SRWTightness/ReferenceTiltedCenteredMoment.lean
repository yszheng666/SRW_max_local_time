import SRWTightness.ReferenceTiltedThirdMoment
import SRWTightness.NonnegativeCenteredThirdMoment

open MeasureTheory

namespace SRWTightness

/-- The actual signed tilted law has a dimension-free third centered absolute moment bound
for every probability-weighted observation. -/
theorem referenceMark_tilted_weighted_centered_third (D K : Finset Site) (hKD : K ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1)
    (w : K → ℝ) (hw : ∀ z, 0 ≤ w z) (hw1 : ∑ z, w z = 1)
    (β : K → ℝ) (L : ℝ) (hL : 0 < L) (hαL : α ≤ L)
    (hG : ∀ z : K, killedGreen D z z ≤ L)
    (hsmall : (∑ z, |β z|) ≤ 1 / (8 * L)) :
    let ν := (referenceMarkLaw D K α).tilted (fun Y : Mark K ↦ ∑ z, β z * (Y z : ℝ))
    let U := fun Y : Mark K ↦ ∑ z, w z * (Y z : ℝ)
    Integrable U ν ∧
    Integrable (fun Y ↦ |U Y - ∫ V, U V ∂ν| ^ 3) ν ∧
    (∫ Y, |U Y - ∫ V, U V ∂ν| ^ 3 ∂ν) ≤ 5898244 * L ^ 3 := by
  let ν := (referenceMarkLaw D K α).tilted (fun Y : Mark K ↦ ∑ z, β z * (Y z : ℝ))
  have hB8 := (le_div_iff₀ (by positivity : 0 < 8 * L)).mp hsmall
  have hB4 : (∑ z, |β z|) ≤ 1 / (4 * L) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have hB0 : 0 ≤ ∑ z, |β z| := Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
    nlinarith
  letI : IsProbabilityMeasure ν :=
    referenceMark_linear_tilt_probability D K hKD α hα hcap β L hL hG hB4
  have hr := referenceMark_tilted_weighted_third_moment D K hKD α hα hcap w hw hw1
    β L hL hαL hG hsmall
  have hc := nonnegative_centered_third_moment ν
    (fun Y : Mark K ↦ ∑ z, w z * (Y z : ℝ)) (by fun_prop)
    (fun Y ↦ Finset.sum_nonneg (fun z _ ↦ mul_nonneg (hw z) (Nat.cast_nonneg _))) hr.1
  refine ⟨hc.1, hc.2.1, hc.2.2.trans ?_⟩
  calc
    _ ≤ 2 * (2949122 * L ^ 3) := mul_le_mul_of_nonneg_left hr.2 (by norm_num)
    _ = _ := by ring

end SRWTightness
