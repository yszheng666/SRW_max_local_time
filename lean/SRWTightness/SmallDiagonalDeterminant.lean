import SRWTightness.SmallDiagonalResolvent
import SRWTightness.DeterminantHalfBound
import SRWTightness.MatrixQuadraticSpectrumBounds

open Matrix

namespace SRWTightness

theorem diagonal_sandwich_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) (hK : K.PosDef) (e : ι → ℝ) :
    (diagonalSquareRoot e * K⁻¹ * diagonalSquareRoot e).PosSemidef := by
  have h := hK.inv.posSemidef.mul_mul_conjTranspose_same (diagonalSquareRoot e)
  have hb : (diagonalSquareRoot e)ᴴ = diagonalSquareRoot e :=
    (Matrix.isHermitian_diagonal _).eq
  rwa [hb] at h

theorem diagonal_sandwich_trace_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) (hK : IsUnit K) (c : ℝ) (hc : 0 < c)
    (hlo : ∀ x : ι → ℝ, c * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (K *ᵥ x))
    (e : ι → ℝ) (he : ∀ i, 0 ≤ e i) :
    (diagonalSquareRoot e * K⁻¹ * diagonalSquareRoot e).trace ≤ (∑ i, e i) / c := by
  have hdiag (i : ι) : K⁻¹ i i ≤ 1 / c := by
    have h := inverse_quadratic_le_of_lower K hK c hc hlo (Pi.single i 1)
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h
  rw [Matrix.trace_mul_cycle, diagonalSquareRoot_square e he]
  have ht : (Matrix.diagonal e * K⁻¹).trace = ∑ i, e i * K⁻¹ i i := by
    simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_mul]
  rw [ht, Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  have hh := mul_le_mul_of_nonneg_left (hdiag i) (he i)
  simpa only [mul_one_div] using hh

/-- The normalization factor is controlled by the sum of the diagonal errors. -/
theorem smallDiagonal_determinant_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) (hK : K.PosDef) (c : ℝ) (hc : 0 < c)
    (hlo : ∀ x : ι → ℝ, c * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (K *ᵥ x))
    (e : ι → ℝ) (he : ∀ i, 0 ≤ e i) (hesmall : ∀ i, e i ≤ c / 2) :
    1 ≤ (Real.sqrt (1 - diagonalSquareRoot e * K⁻¹ * diagonalSquareRoot e).det)⁻¹ ∧
    (Real.sqrt (1 - diagonalSquareRoot e * K⁻¹ * diagonalSquareRoot e).det)⁻¹ ≤
      Real.exp ((∑ i, e i) / c) := by
  let J := diagonalSquareRoot e * K⁻¹ * diagonalSquareRoot e
  have hJ : J.PosSemidef := diagonal_sandwich_posSemidef K hK e
  have hA : (1 - J).IsHermitian := Matrix.isHermitian_one.sub hJ.isHermitian
  have hl := smallDiagonal_resolvent_lower K hK.isUnit c hc hlo e he hesmall
  have hu (y : ι → ℝ) : y ⬝ᵥ ((1 - J) *ᵥ y) ≤ 1 * (∑ i, y i ^ 2) := by
    have hn := hJ.dotProduct_mulVec_nonneg y
    simp only [star_trivial] at hn
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, one_mul]
    have hy : y ⬝ᵥ y = ∑ i, y i ^ 2 := by simp only [dotProduct, pow_two]
    rw [hy]
    linarith
  have hb := eigenvalues_bounds_of_quadratic (1 - J) hA (1 / 2) 1 hl hu
  have hd := determinant_inverse_sqrt_bounds (1 - J) hA (fun i ↦ (hb i).1) (fun i ↦ (hb i).2)
  have ht : (Fintype.card ι : ℝ) - (1 - J).trace = J.trace := by
    rw [Matrix.trace_sub, Matrix.trace_one]
    ring
  rw [ht] at hd
  exact ⟨hd.1, hd.2.trans (Real.exp_le_exp.mpr (diagonal_sandwich_trace_bound K hK.isUnit c hc hlo e he))⟩

end SRWTightness
