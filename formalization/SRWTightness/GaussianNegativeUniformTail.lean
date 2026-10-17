import SRWTightness.GaussianShiftedBranches
import SRWTightness.GreenHarmonic

open MeasureTheory ProbabilityTheory
namespace SRWTightness

/-- A common diagonal bound turns the negative branch into a cardinality Gaussian error. -/
theorem gaussian_negative_tail_sum_uniform (D A : Finset Site) (hAD : A ⊆ D)
    (s V : ℝ) (hs : 0 ≤ s) (hV : 0 < V)
    (hdiag : ∀ z : A, killedGreen D z z ≤ V) :
    (∑ z : A, Real.exp (-s ^ 2 / (2 * killedGreen D z z))) ≤
      (A.card : ℝ) * Real.exp (-s ^ 2 / (2 * V)) := by
  have hz (z : A) : 0 < killedGreen D z z := by
    have hh := killedGreen_diag_ge_one D z (hAD z.property)
    linarith
  have he (z : A) : Real.exp (-s ^ 2 / (2 * killedGreen D z z)) ≤
      Real.exp (-s ^ 2 / (2 * V)) := by
    apply Real.exp_le_exp.mpr
    have hd := div_le_div_of_nonneg_left (sq_nonneg s)
      (show 0 < 2 * killedGreen D z z from mul_pos (by norm_num) (hz z))
      (show 2 * killedGreen D z z ≤ 2 * V by linarith [hdiag z])
    simpa only [neg_div] using neg_le_neg hd
  have hsum := Finset.sum_le_sum (fun z (_ : z ∈ (Finset.univ : Finset A)) ↦ he z)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul] using hsum

theorem gaussian_negative_max_uniform_tail (D A : Finset Site) (hAD : A ⊆ D)
    (s V : ℝ) (hs : 0 ≤ s) (hV : 0 < V)
    (hdiag : ∀ z : A, killedGreen D z z ≤ V) :
    (gaussianGreenLaw D A).real {φ | ∃ z : A, s ≤ -φ z} ≤
      (A.card : ℝ) * Real.exp (-s ^ 2 / (2 * V)) := by
  exact (gaussianGreenLaw_negative_max_tail D A hAD s hs).trans
    (gaussian_negative_tail_sum_uniform D A hAD s V hs hV hdiag)

end SRWTightness
