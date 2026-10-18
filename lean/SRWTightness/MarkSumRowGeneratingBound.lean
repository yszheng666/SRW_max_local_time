import SRWTightness.ReferenceRowGeneratingBound

open MeasureTheory

namespace SRWTightness

/-- Independent actual marks turn the row-resolvent bound into an exponential moment estimate. -/
theorem markSum_row_generating_bound
    (hOcc : FiniteOccupationRowIntegrabilityInput) (hRes : FiniteResolventRowBoundInput)
    (D A : Finset Site) (hAD : A ⊆ D) (α : ℝ) (hα : 0 ≤ α)
    (hcap : α * capacity D A ≤ 1) (r W : ℝ) (hr : 0 ≤ r) (hW : 0 ≤ W)
    (hsmall : r * W < 1)
    (hrow : ∀ y : A, ∑ z : A, |killedGreen D y z - (if y = z then 1 else 0)| ≤ r)
    (k : ℕ) :
    (∫ Y, markMonomial (fun _ : A ↦ 1 + W) (sumMarks A k Y) ∂markProductLaw D A α k) ≤
      Real.exp (α * (Fintype.card A : ℝ) * k * W / (1 - r * W)) := by
  have hb := (referenceMark_row_generating_bound hOcc hRes D A hAD α hα hcap
    r W hr hW hsmall hrow).2
  have hp : 0 ≤ ∫ Y, markMonomial (fun _ : A ↦ 1 + W) Y ∂referenceMarkLaw D A α := by
    apply integral_nonneg
    intro Y
    unfold markMonomial
    exact Finset.prod_nonneg (fun _ _ ↦ pow_nonneg (by linarith) _)
  have he : 1 + α * (Fintype.card A : ℝ) * W / (1 - r * W) ≤
      Real.exp (α * (Fintype.card A : ℝ) * W / (1 - r * W)) := by
    linarith [Real.add_one_le_exp (α * (Fintype.card A : ℝ) * W / (1 - r * W))]
  rw [integral_markMonomial_sum D A α hα hcap k]
  calc
    _ ≤ (Real.exp (α * (Fintype.card A : ℝ) * W / (1 - r * W))) ^ k :=
      pow_le_pow_left₀ hp (hb.trans he) k
    _ = _ := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

end SRWTightness
