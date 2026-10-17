import SRWTightness.BrownianIncrementCovariance

open Matrix

namespace SRWTightness

theorem quadratic_sub_diagonal {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) (e x : Fin n → ℝ) :
    (∑ i, ∑ j, x i * (K - Matrix.diagonal e) i j * x j) =
      (∑ i, ∑ j, x i * K i j * x j) - ∑ i, e i * x i ^ 2 := by
  have ht (i j : Fin n) : x i * (Matrix.diagonal e) i j * x j =
      if i = j then e i * x i ^ 2 else 0 := by
    by_cases he : i = j
    · subst j; simp; ring
    · simp [Matrix.diagonal_apply, he]
  simp only [Matrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib, ht]
  simp

/-- A small diagonal correction preserves a dimension-independent covariance lower bound. -/
theorem incrementCovariance_sub_diagonal_lower {n : ℕ} (d e x : Fin n → ℝ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hd : ∀ i, δ ≤ d i) (he : ∀ i, e i ≤ δ / 8) :
    (δ / 8) * (∑ i, x i ^ 2) ≤
      ∑ i, ∑ j, x i * (incrementCovariance d - Matrix.diagonal e) i j * x j := by
  rw [quadratic_sub_diagonal]
  have hq := incrementCovariance_quadratic_lower d x δ hδ hd
  have hc : (∑ i, e i * x i ^ 2) ≤ (δ / 8) * ∑ i, x i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ ↦ mul_le_mul_of_nonneg_right (he i) (sq_nonneg _))
  linarith

theorem incrementCovariance_sub_diagonal_posDef {n : ℕ} (d e : Fin n → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (hd : ∀ i, δ ≤ d i) (he : ∀ i, e i ≤ δ / 8) :
    (incrementCovariance d - Matrix.diagonal e).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · exact (incrementCovariance_posDef d δ hδ hd).isHermitian.sub (Matrix.isHermitian_diagonal e)
  · intro x hx
    have hex : ∃ i, x i ≠ 0 := by
      by_contra! hh
      exact hx (funext hh)
    obtain ⟨i, hi⟩ := hex
    have hs : 0 < ∑ i, x i ^ 2 :=
      (Finset.sum_pos_iff_of_nonneg (fun j _ ↦ sq_nonneg (x j))).mpr ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩
    have hh := (mul_pos (div_pos hδ (by norm_num)) hs).trans_le
      (incrementCovariance_sub_diagonal_lower d e x δ hδ.le hd he)
    simpa only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, Finset.mul_sum, mul_assoc] using hh

end SRWTightness
