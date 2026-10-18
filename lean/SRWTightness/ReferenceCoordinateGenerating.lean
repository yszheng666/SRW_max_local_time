import SRWTightness.ReferenceTail
import SRWTightness.NaturalExponentialMoment

open MeasureTheory

namespace SRWTightness

/-- Integrability up to the exact geometric convergence radius of one reference coordinate. -/
theorem referenceMark_coordinate_pow_integrable (D K : Finset Site) (hKD : K ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1) (z : K) (b : ℝ)
    (hb : 0 ≤ b) (hqb : (1 - 1 / killedGreen D z z) * b < 1) :
    Integrable (fun Y : Mark K ↦ b ^ Y z) (referenceMarkLaw D K α) := by
  letI := referenceMarkLaw_isProbabilityMeasure D K α hα hcap
  have hg := killedGreen_diag_ge_one D z (hKD z.property)
  have hgp : 0 < killedGreen D z z := by linarith
  apply integrable_pow_of_nat_geometric_tail _ (fun Y : Mark K ↦ Y z)
    (measurable_pi_apply z) (α / killedGreen D z z) (1 - 1 / killedGreen D z z) b
    (by apply sub_nonneg.mpr; exact (div_le_one hgp).mpr hg) hb hqb
  intro n
  rw [referenceMark_tail D K hKD α hα hcap z (n + 1) (by omega)]
  simp

/-- Exact scalar generating function for actual marks, including positive tilts. -/
theorem referenceMark_coordinate_generating (D K : Finset Site) (hKD : K ⊆ D)
    (α : ℝ) (hα : 0 ≤ α) (hcap : α * capacity D K ≤ 1) (z : K) (b : ℝ)
    (hb : 0 ≤ b) (hqb : (1 - 1 / killedGreen D z z) * b < 1) :
    (∫ Y : Mark K, b ^ Y z ∂referenceMarkLaw D K α) =
      1 + α * (b - 1) / (1 - (killedGreen D z z - 1) * (b - 1)) := by
  let μ := referenceMarkLaw D K α
  let ν := μ.map (fun Y : Mark K ↦ Y z)
  let G := killedGreen D z z
  let q := 1 - 1 / G
  letI := referenceMarkLaw_isProbabilityMeasure D K α hα hcap
  have hg : 1 ≤ G := killedGreen_diag_ge_one D z (hKD z.property)
  have hg0 : 0 < G := by linarith
  have hq : 0 ≤ q := by dsimp [q]; exact sub_nonneg.mpr ((div_le_one hg0).mpr hg)
  have hn : ‖q * b‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hq hb)]; exact hqb
  have hi := referenceMark_coordinate_pow_integrable D K hKD α hα hcap z b hb hqb
  have hm (n : ℕ) : ν.real {n} = μ.real {Y | Y z = n} := by
    unfold Measure.real ν
    rw [Measure.map_apply (measurable_pi_apply z) (measurableSet_singleton n)]
    rfl
  have hs (n : ℕ) : ν.real {n + 1} * b ^ (n + 1) =
      (α * G⁻¹ ^ 2 * b) * (q * b) ^ n := by
    rw [hm, referenceMark_positive_mass D K hKD α hα hcap z (n + 1) (by omega)]
    simp only [Nat.add_sub_cancel, pow_succ, mul_pow]
    dsimp [G, q]
    ring
  have hsum : Summable (fun n : ℕ ↦ ν.real {n + 1} * b ^ (n + 1)) := by
    simp_rw [hs]
    exact (summable_geometric_of_norm_lt_one hn).mul_left _
  have hall : Summable (fun n : ℕ ↦ ν.real {n} * b ^ n) :=
    (summable_nat_add_iff 1).mp hsum
  have hiν : Integrable (fun n : ℕ ↦ b ^ n) ν :=
    (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
      (measurable_pi_apply z).aemeasurable).mpr hi
  rw [← integral_map (measurable_pi_apply z).aemeasurable
    (measurable_of_countable (fun n : ℕ ↦ b ^ n)).aestronglyMeasurable,
    integral_countable hiν]
  simp only [smul_eq_mul]
  rw [hall.tsum_eq_zero_add, hm, referenceMark_zero_mass D K hKD α hα hcap z]
  simp only [pow_zero, mul_one]
  simp_rw [hs]
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hn]
  have hd : 1 - (G - 1) * (b - 1) = G * (1 - q * b) := by dsimp [q]; field_simp <;> ring
  have hden : 1 - q * b ≠ 0 := by linarith [hqb]
  change 1 - α / G + α * G⁻¹ ^ 2 * b * (1 - q * b)⁻¹ =
    1 + α * (b - 1) / (1 - (G - 1) * (b - 1))
  rw [hd]
  have hrel : G * q = G - 1 := by dsimp [q]; field_simp <;> ring
  generalize hqq : q = Q at *
  have hden' : 1 - b * Q ≠ 0 := by simpa only [mul_comm] using hden
  field_simp [hg0.ne', hden, hden']
  linear_combination α * b * hrel

end SRWTightness
