import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open Matrix

namespace SRWTightness

/-- Above one half, the logarithmic entropy error is quadratic in the displacement from one. -/
theorem log_entropy_error_bound (x : ℝ) (hx : (1 / 2 : ℝ) ≤ x) :
    0 ≤ x - 1 - Real.log x ∧ x - 1 - Real.log x ≤ 2 * (x - 1) ^ 2 := by
  have hp : 0 < x := by linarith
  have hl := Real.log_le_sub_one_of_pos hp
  have hn : 0 ≤ x - 1 - Real.log x := by linarith
  have hlog := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hp) hp.le
  rw [mul_sub, mul_one, mul_inv_cancel₀ hp.ne'] at hlog
  have hm := mul_le_mul_of_nonneg_right hx hn
  constructor
  · exact hn
  · nlinarith

/-- The matrix trace/log-determinant error is bounded by squared spectral perturbations. -/
theorem matrix_trace_logdet_spectral_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (hG : G.PosDef)
    (hgap : ∀ i, (1 / 2 : ℝ) ≤ hG.isHermitian.eigenvalues i) :
    0 ≤ Matrix.trace G - Fintype.card ι - Real.log G.det ∧
    Matrix.trace G - Fintype.card ι - Real.log G.det ≤
      2 * ∑ i, (hG.isHermitian.eigenvalues i - 1) ^ 2 := by
  have he : Matrix.trace G - Fintype.card ι - Real.log G.det =
      ∑ i, (hG.isHermitian.eigenvalues i - 1 - Real.log (hG.isHermitian.eigenvalues i)) := by
    rw [hG.isHermitian.trace_eq_sum_eigenvalues, hG.isHermitian.det_eq_prod_eigenvalues]
    simp only [RCLike.ofReal_real_eq_id, id_eq]
    rw [Real.log_prod (fun i _ ↦ (hG.eigenvalues_pos i).ne')]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [he]
  constructor
  · exact Finset.sum_nonneg (fun i _ ↦ (log_entropy_error_bound _ (hgap i)).1)
  · calc
      _ ≤ ∑ i, 2 * (hG.isHermitian.eigenvalues i - 1) ^ 2 :=
        Finset.sum_le_sum (fun i _ ↦ (log_entropy_error_bound _ (hgap i)).2)
      _ = _ := (Finset.mul_sum _ _ _).symm

end SRWTightness
