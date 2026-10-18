import SRWTightness.MatrixLogDetError
import Mathlib.Analysis.InnerProductSpace.PiL2

open Matrix WithLp

namespace SRWTightness

/-- Unitary conjugation preserves the matrix trace. -/
theorem matrix_unitary_conjugate_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : unitary (Matrix ι ι ℝ)) (A : Matrix ι ι ℝ) :
    Matrix.trace (Unitary.conjStarAlgAut ℝ _ U A) = Matrix.trace A := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul]

/-- The squared Frobenius distance of a Hermitian matrix from identity is its spectral error sum. -/
theorem hermitian_identity_frobenius_spectral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (hG : G.IsHermitian) :
    (∑ i, ∑ j, (G - 1) i j ^ 2) = ∑ i, (hG.eigenvalues i - 1) ^ 2 := by
  let e := Unitary.conjStarAlgAut ℝ _ hG.eigenvectorUnitary
  let D : Matrix ι ι ℝ := diagonal (fun i ↦ hG.eigenvalues i)
  have hGD : G = e D := by
    simpa only [e, D, RCLike.ofReal_real_eq_id, Function.id_comp] using hG.spectral_theorem
  have he : (G - 1) ^ 2 = e ((D - 1) ^ 2) := by rw [map_pow, map_sub, map_one, ← hGD]
  have htrace : Matrix.trace ((G - 1) ^ 2) = ∑ i, (hG.eigenvalues i - 1) ^ 2 := by
    rw [he, matrix_unitary_conjugate_trace]
    have hd : D - 1 = diagonal (fun i ↦ hG.eigenvalues i - 1) := by
      dsimp only [D]
      rw [← Matrix.diagonal_one, ← Matrix.diagonal_sub]
    rw [hd, Matrix.diagonal_pow, Matrix.trace_diagonal]
    rfl
  have hsym (i j : ι) : (G - 1) j i = (G - 1) i j := by
    have hh := congrArg (fun M : Matrix ι ι ℝ ↦ M i j) (hG.sub isHermitian_one).eq
    simpa only [Matrix.conjTranspose_apply, star_trivial] using hh
  rw [← htrace, pow_two]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hsym, pow_two]

/-- A fixed spectral floor controls the trace/log-determinant error by squared Frobenius distance. -/
theorem matrix_trace_logdet_frobenius_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℝ) (hG : G.PosDef)
    (hgap : ∀ i, (1 / 2 : ℝ) ≤ hG.isHermitian.eigenvalues i) :
    0 ≤ Matrix.trace G - Fintype.card ι - Real.log G.det ∧
    Matrix.trace G - Fintype.card ι - Real.log G.det ≤
      2 * ‖(toLp 2 (fun ij : ι × ι ↦ (G - 1) ij.1 ij.2) : EuclideanSpace ℝ (ι × ι))‖ ^ 2 := by
  have hh := matrix_trace_logdet_spectral_bound G hG hgap
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Fintype.sum_prod_type]
  rw [hermitian_identity_frobenius_spectral G hG.isHermitian]
  exact hh

end SRWTightness
