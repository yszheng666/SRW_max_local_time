import SRWTightness.ReferenceTiltedCovarianceDerivative
import SRWTightness.ReferenceTiltedCenteredMoment
import SRWTightness.ReferenceSignedCenteredMoment

open MeasureTheory ProbabilityTheory

namespace SRWTightness

/-- The derivative of an actual tilted covariance is bounded by L³ times the physical l1 norm. -/
theorem referenceMark_tilted_covariance_deriv_bound (D K : Finset Site) (hKD : K ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1)
    (w v : K → ℝ) (hw : ∀ z, 0 ≤ w z) (hv : ∀ z, 0 ≤ v z)
    (hw1 : ∑ z, w z = 1) (hv1 : ∑ z, v z = 1) (β : K → ℝ)
    (L : ℝ) (hL : 0 < L) (hαL : α ≤ L) (hG : ∀ z : K, killedGreen D z z ≤ L)
    (s : ℝ) (hs : |s| * (∑ z, |β z|) < 1 / (8 * L)) :
    let H := fun Y : Mark K ↦ ∑ z, w z * (Y z : ℝ)
    let J := fun Y : Mark K ↦ ∑ z, v z * (Y z : ℝ)
    let X := fun Y : Mark K ↦ ∑ z, β z * (Y z : ℝ)
    let μ := referenceMarkLaw D K α
    |deriv (fun t ↦ covariance H J (μ.tilted (fun Y ↦ t * X Y))) s| ≤
      35389464 * L ^ 3 * (∑ z, |β z|) := by
  let H := fun Y : Mark K ↦ ∑ z, w z * (Y z : ℝ)
  let J := fun Y : Mark K ↦ ∑ z, v z * (Y z : ℝ)
  let X := fun Y : Mark K ↦ ∑ z, β z * (Y z : ℝ)
  let μ := referenceMarkLaw D K α
  let ν := μ.tilted (fun Y ↦ s * X Y)
  let B := ∑ z, |β z|
  have hd := referenceMark_hasDerivAt_tilted_covariance D K hKD α hα hcap
    w v hw hv hw1 hv1 β L hL hG s hs
  dsimp only at hd ⊢
  rw [hd.deriv]
  change |∫ Y, (H Y - ∫ Z, H Z ∂ν) * (J Y - ∫ Z, J Z ∂ν) *
    (X Y - ∫ Z, X Z ∂ν) ∂ν| ≤ 35389464 * L ^ 3 * B
  by_cases hB : B = 0
  · have hz (z : K) : β z = 0 := by
      apply abs_eq_zero.mp
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun z _ ↦ abs_nonneg (β z))).mp hB
        z (Finset.mem_univ z)
    simp [X, hz, hB]
  have hBpos : 0 < B := lt_of_le_of_ne (Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)) (Ne.symm hB)
  let a := fun z ↦ β z / B
  let U := fun Y : Mark K ↦ ∑ z, a z * (Y z : ℝ)
  have ha : ∑ z, |a z| = 1 := by
    simp only [a, abs_div, abs_of_pos hBpos, ← Finset.sum_div]
    exact div_self hB
  have hsmall : (∑ z, |s * β z|) ≤ 1 / (8 * L) := by
    simpa only [abs_mul, ← Finset.mul_sum] using hs.le
  have htilt : (fun Y : Mark K ↦ ∑ z, (s * β z) * (Y z : ℝ)) = (fun Y ↦ s * X Y) := by
    funext Y
    dsimp [X]
    simp only [Finset.mul_sum, mul_assoc]
  have hH := referenceMark_tilted_weighted_centered_third D K hKD α hα hcap w hw hw1
    (fun z ↦ s * β z) L hL hαL hG hsmall
  have hJ := referenceMark_tilted_weighted_centered_third D K hKD α hα hcap v hv hv1
    (fun z ↦ s * β z) L hL hαL hG hsmall
  have hU := referenceMark_tilted_signed_centered_third D K hKD α hα hcap a ha
    (fun z ↦ s * β z) L hL hαL hG hsmall
  dsimp only at hH hJ hU
  rw [htilt] at hH hJ hU
  have htr := third_product_moment_bound ν
    (fun Y ↦ H Y - ∫ Z, H Z ∂ν) (fun Y ↦ J Y - ∫ Z, J Z ∂ν)
    (fun Y ↦ U Y - ∫ Z, U Z ∂ν)
    (by dsimp [H]; fun_prop) (by dsimp [J]; fun_prop) (by dsimp [U]; fun_prop)
    hH.2.1 hJ.2.1 hU.2.1
  have hbound : |∫ Y, (H Y - ∫ Z, H Z ∂ν) * (J Y - ∫ Z, J Z ∂ν) *
      (U Y - ∫ Z, U Z ∂ν) ∂ν| ≤ 35389464 * L ^ 3 := by
    have hh := htr.2
    have hhH := hH.2.2
    have hhJ := hJ.2.2
    have hhU := hU.2.2
    change (∫ Y, |H Y - ∫ Z, H Z ∂ν| ^ 3 ∂ν) ≤ 5898244 * L ^ 3 at hhH
    change (∫ Y, |J Y - ∫ Z, J Z ∂ν| ^ 3 ∂ν) ≤ 5898244 * L ^ 3 at hhJ
    change (∫ Y, |U Y - ∫ Z, U Z ∂ν| ^ 3 ∂ν) ≤ 23592976 * L ^ 3 at hhU
    linarith
  have hX : X = fun Y ↦ B * U Y := by
    funext Y
    dsimp [X, U, a]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    field_simp
  have he : (fun Y ↦ (H Y - ∫ Z, H Z ∂ν) * (J Y - ∫ Z, J Z ∂ν) *
      (X Y - ∫ Z, X Z ∂ν)) =
        (fun Y ↦ B * ((H Y - ∫ Z, H Z ∂ν) * (J Y - ∫ Z, J Z ∂ν) *
          (U Y - ∫ Z, U Z ∂ν))) := by
    funext Y
    rw [hX, integral_const_mul]
    ring
  rw [he, integral_const_mul, abs_mul, abs_of_pos hBpos]
  calc
    _ ≤ B * (35389464 * L ^ 3) := mul_le_mul_of_nonneg_left hbound hBpos.le
    _ = _ := by ring

end SRWTightness
