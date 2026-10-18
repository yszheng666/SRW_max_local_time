import SRWTightness.ReferenceCoordinateGenerating

open MeasureTheory

namespace SRWTightness

/-- Quantitative exponential control for one actual mark coordinate on its Green-function scale. -/
theorem referenceMark_coordinate_exponential_bound (D K : Finset Site) (hKD : K ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1) (z : K) (s : ℝ)
    (hs : 0 ≤ s) (hsmall : s ≤ 1 / (4 * killedGreen D z z)) :
    Integrable (fun Y : Mark K ↦ Real.exp (s * (Y z : ℝ))) (referenceMarkLaw D K α) ∧
    (∫ Y : Mark K, Real.exp (s * (Y z : ℝ)) ∂referenceMarkLaw D K α) ≤ 1 + 4 * α * s := by
  let G := killedGreen D z z
  have hg : 1 ≤ G := killedGreen_diag_ge_one D z (hKD z.property)
  have hg0 : 0 < G := by linarith
  have hsg : s * (4 * G) ≤ 1 := (le_div_iff₀ (by positivity)).mp hsmall
  have hsquarter : s ≤ 1 / 4 := by nlinarith
  have he := Real.exp_bound_div_one_sub_of_interval hs (by linarith : s < 1)
  have hemul := (le_div_iff₀ (by linarith : 0 < 1 - s)).mp he
  have he2 : Real.exp s - 1 ≤ 2 * s := by
    have hh : 1 / (1 - s) ≤ 1 + 2 * s := by
      apply (div_le_iff₀ (by linarith : 0 < 1 - s)).mpr
      nlinarith
    linarith
  have he0 : 0 ≤ Real.exp s - 1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr hs)
  have hGe : G * (Real.exp s - 1) ≤ 1 / 2 := by nlinarith
  have hGe1 : (G - 1) * (Real.exp s - 1) ≤ 1 / 2 := by nlinarith
  have hqb : (1 - 1 / G) * Real.exp s < 1 := by
    have hid : (1 - (1 - 1 / G) * Real.exp s) * G =
        1 - (G - 1) * (Real.exp s - 1) := by field_simp <;> ring
    nlinarith [Real.exp_pos s]
  have hfun : (fun Y : Mark K ↦ Real.exp (s * (Y z : ℝ))) =
      (fun Y : Mark K ↦ (Real.exp s) ^ Y z) := by
    funext Y
    rw [mul_comm, Real.exp_nat_mul]
  rw [hfun]
  refine ⟨referenceMark_coordinate_pow_integrable D K hKD α hα hcap z _
    (Real.exp_pos s).le hqb, ?_⟩
  rw [referenceMark_coordinate_generating D K hKD α hα hcap z _ (Real.exp_pos s).le hqb]
  have hden : 0 < 1 - (G - 1) * (Real.exp s - 1) := by linarith
  have hnum : 0 ≤ α * (Real.exp s - 1) := mul_nonneg hα he0
  have hfrac : α * (Real.exp s - 1) / (1 - (G - 1) * (Real.exp s - 1)) ≤
      2 * (α * (Real.exp s - 1)) := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg hnum (show 0 ≤ 1 / 2 - (G - 1) * (Real.exp s - 1) by linarith)]
  have hlin := mul_le_mul_of_nonneg_left he2 hα
  change 1 + α * (Real.exp s - 1) / (1 - (G - 1) * (Real.exp s - 1)) ≤ _
  linarith

end SRWTightness
