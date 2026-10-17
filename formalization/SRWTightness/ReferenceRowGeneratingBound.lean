import SRWTightness.FiniteOccupationRowInputs

open MeasureTheory Matrix

namespace SRWTightness

/-- The actual reference mark has the positive generating bound dictated by the G-I row sum. -/
theorem referenceMark_row_generating_bound
    (hOcc : FiniteOccupationRowIntegrabilityInput) (hRes : FiniteResolventRowBoundInput)
    (D A : Finset Site) (hAD : A ⊆ D) (α : ℝ) (hα : 0 ≤ α)
    (hcap : α * capacity D A ≤ 1) (r W : ℝ) (hr : 0 ≤ r) (hW : 0 ≤ W)
    (hsmall : r * W < 1)
    (hrow : ∀ y : A, ∑ z : A, |killedGreen D y z - (if y = z then 1 else 0)| ≤ r) :
    Integrable (markMonomial (fun _ : A ↦ 1 + W)) (referenceMarkLaw D A α) ∧
    (∫ Y, markMonomial (fun _ : A ↦ 1 + W) Y ∂referenceMarkLaw D A α) ≤
      1 + α * (Fintype.card A : ℝ) * W / (1 - r * W) := by
  classical
  let M := (observationGreen D A - 1) * Matrix.diagonal (fun _ : A ↦ W)
  have hM (y : A) : (∑ z : A, |M y z|) ≤ r * W := by
    simp only [M, Matrix.mul_diagonal, observationGreen, Matrix.sub_apply, Matrix.one_apply,
      abs_mul, abs_of_nonneg hW, ← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hrow y) hW
  have hrow' (y : A) : (∑ z : A,
      |killedGreen D y z - (if y = z then 1 else 0)| * |(1 + W) - 1|) < 1 := by
    simp only [show 1 + W - 1 = W by ring, abs_of_nonneg hW, ← Finset.sum_mul]
    exact (mul_le_mul_of_nonneg_right (hrow y) hW).trans_lt hsmall
  have hi := hOcc D A hAD (fun _ ↦ 1 + W) (fun _ ↦ by linarith) hrow'
  have hiRef : Integrable (markMonomial (fun _ : A ↦ 1 + W)) (referenceMarkLaw D A α) := by
    apply integrable_referenceMark
    intro x hx
    exact (integrable_map_measure (measurable_markMonomial _).aestronglyMeasurable
      (measurable_killedMark D A x).aemeasurable).mpr (hi x)
  refine ⟨hiRef, ?_⟩
  have he : observationResolventMatrix D A (fun _ ↦ 1 + W) = 1 - M := by
    simp only [observationResolventMatrix, show 1 + W - 1 = W by ring, M]
  have hb := hRes A M (r * W) (mul_nonneg hr hW) hsmall hM
  rw [← he] at hb
  have hf := referenceMark_observation_generating_integrable D A hAD α hα hcap
    (fun _ ↦ 1 + W) hi (observationResolvent_isUnit_of_row_sum D A _ hrow')
  simp only [show 1 + W - 1 = W by ring] at hf
  have hs : (∑ z : A, W * ((observationResolventMatrix D A (fun _ ↦ 1 + W))⁻¹.mulVec 1) z) ≤
      (Fintype.card A : ℝ) * (W / (1 - r * W)) := by
    calc
      _ ≤ ∑ _z : A, W * (1 / (1 - r * W)) :=
        Finset.sum_le_sum (fun z _ ↦ mul_le_mul_of_nonneg_left
          ((le_abs_self _).trans (hb z)) hW)
      _ = _ := by simp [div_eq_mul_inv]
  rw [hf]
  calc
    _ ≤ 1 + α * ((Fintype.card A : ℝ) * (W / (1 - r * W))) :=
      by linarith [mul_le_mul_of_nonneg_left hs hα]
    _ = _ := by ring

end SRWTightness
