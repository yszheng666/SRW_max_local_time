import SRWTightness.DiagonalSquareRootCorrection

open Matrix

namespace SRWTightness

/-- A coordinatewise diagonal bound suffices for the resolvent lower bound. -/
theorem smallDiagonal_resolvent_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) (hK : IsUnit K) (c : ℝ) (hc : 0 < c)
    (hlo : ∀ x : ι → ℝ, c * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (K *ᵥ x))
    (e : ι → ℝ) (he : ∀ i, 0 ≤ e i) (hesmall : ∀ i, e i ≤ c / 2)
    (y : ι → ℝ) :
    (1 / 2 : ℝ) * (∑ i, y i ^ 2) ≤
      y ⬝ᵥ ((1 - diagonalSquareRoot e * K⁻¹ * diagonalSquareRoot e) *ᵥ y) := by
  have hi := inverse_quadratic_le_of_lower K hK c hc hlo (diagonalSquareRoot e *ᵥ y)
  rw [diagonalSquareRoot_energy e y he] at hi
  have hs : (∑ i, e i * y i ^ 2) ≤ (c / 2) * ∑ i, y i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ ↦ mul_le_mul_of_nonneg_right (hesmall i) (sq_nonneg _))
  have hbound : (diagonalSquareRoot e *ᵥ y) ⬝ᵥ
      (K⁻¹ *ᵥ (diagonalSquareRoot e *ᵥ y)) ≤ (1 / 2 : ℝ) * ∑ i, y i ^ 2 := by
    apply hi.trans
    apply (div_le_iff₀ hc).mpr
    nlinarith
  have heq : y ⬝ᵥ ((diagonalSquareRoot e * K⁻¹ * diagonalSquareRoot e) *ᵥ y) =
      (diagonalSquareRoot e *ᵥ y) ⬝ᵥ (K⁻¹ *ᵥ (diagonalSquareRoot e *ᵥ y)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    conv_lhs => arg 2; arg 1; unfold diagonalSquareRoot; rw [← Matrix.diagonal_transpose (fun i ↦ Real.sqrt (e i))]
    rw [Matrix.dotProduct_transpose_mulVec, dotProduct_comm]
    rfl
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, heq]
  have hy : y ⬝ᵥ y = ∑ i, y i ^ 2 := by simp only [dotProduct, pow_two]
  rw [hy]
  linarith

theorem smallDiagonal_resolvent_posDef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) (hK : K.PosDef) (c : ℝ) (hc : 0 < c)
    (hlo : ∀ x : ι → ℝ, c * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (K *ᵥ x))
    (e : ι → ℝ) (he : ∀ i, 0 ≤ e i) (hesmall : ∀ i, e i ≤ c / 2) :
    (1 - diagonalSquareRoot e * K⁻¹ * diagonalSquareRoot e).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · have hh := (hK.inv.posSemidef.mul_mul_conjTranspose_same (diagonalSquareRoot e)).isHermitian
    have hb : (diagonalSquareRoot e)ᴴ = diagonalSquareRoot e :=
      (Matrix.isHermitian_diagonal _).eq
    rw [hb] at hh
    exact Matrix.isHermitian_one.sub hh
  · intro y hy
    have hex : ∃ i, y i ≠ 0 := by
      by_contra! hh
      exact hy (funext hh)
    obtain ⟨i, hi⟩ := hex
    have hs : 0 < ∑ i, y i ^ 2 :=
      (Finset.sum_pos_iff_of_nonneg (fun j _ ↦ sq_nonneg (y j))).mpr
        ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩
    have hh := smallDiagonal_resolvent_lower K hK.isUnit c hc hlo e he hesmall y
    simp only [star_trivial]
    linarith

end SRWTightness
