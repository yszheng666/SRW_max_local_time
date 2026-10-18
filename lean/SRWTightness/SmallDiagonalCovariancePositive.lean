import SRWTightness.SmallDiagonalResolvent

open Matrix

namespace SRWTightness

theorem quadratic_diagonal_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) (e x : ι → ℝ) :
    x ⬝ᵥ ((K - Matrix.diagonal e) *ᵥ x) = x ⬝ᵥ (K *ᵥ x) - ∑ i, e i * x i ^ 2 := by
  rw [Matrix.sub_mulVec, dotProduct_sub]
  congr 1
  simp only [dotProduct, Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem smallDiagonal_covariance_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) (c : ℝ)
    (hlo : ∀ x : ι → ℝ, c * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (K *ᵥ x))
    (e : ι → ℝ) (hesmall : ∀ i, e i ≤ c / 2) (x : ι → ℝ) :
    (c / 2) * (∑ i, x i ^ 2) ≤ x ⬝ᵥ ((K - Matrix.diagonal e) *ᵥ x) := by
  rw [quadratic_diagonal_sub]
  have hs : (∑ i, e i * x i ^ 2) ≤ (c / 2) * ∑ i, x i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ ↦ mul_le_mul_of_nonneg_right (hesmall i) (sq_nonneg _))
  linarith [hlo x]

theorem smallDiagonal_covariance_posDef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Matrix ι ι ℝ) (hK : K.IsHermitian) (c : ℝ) (hc : 0 < c)
    (hlo : ∀ x : ι → ℝ, c * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (K *ᵥ x))
    (e : ι → ℝ) (hesmall : ∀ i, e i ≤ c / 2) : (K - Matrix.diagonal e).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (hK.sub (Matrix.isHermitian_diagonal e))
  intro x hx
  have hex : ∃ i, x i ≠ 0 := by
    by_contra! hh
    exact hx (funext hh)
  obtain ⟨i, hi⟩ := hex
  have hs : 0 < ∑ i, x i ^ 2 :=
    (Finset.sum_pos_iff_of_nonneg (fun j _ ↦ sq_nonneg (x j))).mpr
      ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩
  have hh := (mul_pos (div_pos hc (by norm_num)) hs).trans_le
    (smallDiagonal_covariance_lower K c hlo e hesmall x)
  simpa only [star_trivial] using hh

end SRWTightness
