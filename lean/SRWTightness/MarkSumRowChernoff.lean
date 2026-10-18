import SRWTightness.MarkSumRowGeneratingBound
import SRWTightness.MarkMonomialConstant

open MeasureTheory

namespace SRWTightness

/-- The actual fixed-mark law satisfies a simultaneous-high-occupation Chernoff bound. -/
theorem markSum_all_high_row_bound
    (hOcc : FiniteOccupationRowIntegrabilityInput) (hRes : FiniteResolventRowBoundInput)
    (D A : Finset Site) (hAD : A ⊆ D) (α : ℝ) (hα : 0 ≤ α)
    (hcap : α * capacity D A ≤ 1) (r W : ℝ) (hr : 0 ≤ r) (hW : 0 ≤ W)
    (hsmall : r * W < 1)
    (hrow : ∀ y : A, ∑ z : A, |killedGreen D y z - (if y = z then 1 else 0)| ≤ r)
    (k : ℕ) (level : ℝ) :
    (markProductLaw D A α k).real {Y | ∀ z : A, level ≤ (sumMarks A k Y z : ℝ)} ≤
      Real.exp (-(Fintype.card A : ℝ) * level * Real.log (1 + W) +
        α * (Fintype.card A : ℝ) * k * W / (1 - r * W)) := by
  letI := referenceMarkLaw_isProbabilityMeasure D A α hα hcap
  letI := markProductLaw_isProbabilityMeasure D A α hα hcap k
  let F := fun Y ↦ markMonomial (fun _ : A ↦ 1 + W) (sumMarks A k Y)
  let ε := Real.exp ((Fintype.card A : ℝ) * level * Real.log (1 + W))
  have hε : 0 < ε := Real.exp_pos _
  have hv : 0 < 1 + W := by linarith
  have hlog : 0 ≤ Real.log (1 + W) := Real.log_nonneg (by linarith)
  have hiRef := (referenceMark_row_generating_bound hOcc hRes D A hAD α hα hcap
    r W hr hW hsmall hrow).1
  have hi : Integrable F (markProductLaw D A α k) := by
    simpa only [F, markMonomial_sum, markProductLaw] using
      (Integrable.fintype_prod (fun _ : Fin k ↦ hiRef))
  have hnon (Y : MarkSamples A k) : 0 ≤ F Y := by
    dsimp [F]
    rw [markMonomial_constant_exp A (1 + W) hv]
    exact Real.exp_nonneg _
  have hsub : {Y : MarkSamples A k | ∀ z : A, level ≤ (sumMarks A k Y z : ℝ)} ⊆
      {Y | ε ≤ F Y} := by
    intro Y hY
    have hs : (Fintype.card A : ℝ) * level ≤ ∑ z : A, (sumMarks A k Y z : ℝ) := by
      simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
        (Finset.sum_le_sum (fun z (_ : z ∈ (Finset.univ : Finset A)) ↦ hY z))
    change ε ≤ F Y
    dsimp [ε, F]
    rw [markMonomial_constant_exp A (1 + W) hv]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hs hlog)
  have hm := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hnon) hi ε
  have hmoment := markSum_row_generating_bound hOcc hRes D A hAD α hα hcap
    r W hr hW hsmall hrow k
  have hp := (mul_le_mul_of_nonneg_left (measureReal_mono hsub) hε.le).trans
    (hm.trans hmoment)
  have hb : (markProductLaw D A α k).real
      {Y | ∀ z : A, level ≤ (sumMarks A k Y z : ℝ)} ≤
      Real.exp (α * (Fintype.card A : ℝ) * k * W / (1 - r * W)) / ε :=
    (le_div_iff₀ hε).mpr (by simpa only [mul_comm] using hp)
  calc
    _ ≤ Real.exp (α * (Fintype.card A : ℝ) * k * W / (1 - r * W)) / ε := hb
    _ = _ := by
      dsimp [ε]
      rw [← Real.exp_sub]
      congr 1
      ring

end SRWTightness
