import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

open Matrix

namespace SRWTightness

theorem inverse_sqrt_le_exp_one_sub (t : ℝ) (hlo : (1 / 2 : ℝ) ≤ t) (hhi : t ≤ 1) :
    (Real.sqrt t)⁻¹ ≤ Real.exp (1 - t) := by
  have ht : 0 < t := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos ht
  have hinv : t⁻¹ - 1 ≤ 2 * (1 - t) := by
    apply (mul_le_mul_iff_right₀ ht).mp
    have he : t⁻¹ * t = 1 := inv_mul_cancel₀ ht.ne'
    nlinarith
  have hb : Real.log ((Real.sqrt t)⁻¹) ≤ 1 - t := by
    rw [Real.log_inv, Real.log_sqrt ht.le]
    linarith
  have hh := Real.exp_le_exp.mpr hb
  rwa [Real.exp_log (inv_pos.mpr (Real.sqrt_pos.mpr ht))] at hh

theorem determinant_inverse_sqrt_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (hlo : ∀ i, (1 / 2 : ℝ) ≤ hA.eigenvalues i) (hhi : ∀ i, hA.eigenvalues i ≤ 1) :
    1 ≤ (Real.sqrt A.det)⁻¹ ∧
      (Real.sqrt A.det)⁻¹ ≤ Real.exp ((Fintype.card ι : ℝ) - A.trace) := by
  have hp (i : ι) : 0 < hA.eigenvalues i := by linarith [hlo i]
  have he : (Real.sqrt A.det)⁻¹ = ∏ i, (Real.sqrt (hA.eigenvalues i))⁻¹ := by
    rw [hA.det_eq_prod_eigenvalues]
    simp only [RCLike.ofReal_real_eq_id, id_eq]
    rw [Real.sqrt_prod Finset.univ (fun i _ ↦ (hp i).le), Finset.prod_inv_distrib]
  rw [he]
  constructor
  · apply Finset.one_le_prod
    intro i _
    have hs : Real.sqrt (hA.eigenvalues i) ≤ 1 := by
      simpa using Real.sqrt_le_sqrt (hhi i)
    exact (one_le_inv₀ (Real.sqrt_pos.mpr (hp i))).mpr hs
  · calc
      _ ≤ ∏ i, Real.exp (1 - hA.eigenvalues i) := by
        apply Finset.prod_le_prod
        · intro i _; positivity
        · intro i _; exact inverse_sqrt_le_exp_one_sub _ (hlo i) (hhi i)
      _ = Real.exp ((Fintype.card ι : ℝ) - A.trace) := by
        rw [← Real.exp_sum, hA.trace_eq_sum_eigenvalues]
        congr 1
        simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          mul_one, RCLike.ofReal_real_eq_id, id_eq]

end SRWTightness
