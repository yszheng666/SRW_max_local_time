import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Matrix

namespace SRWTightness

/-- An entrywise matrix error controls every quadratic form, with explicit dimension factor. -/
theorem entrywise_quadratic_error {ι : Type*} [Fintype ι]
    (A B : Matrix ι ι ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hAB : ∀ i j, |A i j - B i j| ≤ ε) (x : ι → ℝ) :
    |x ⬝ᵥ (A *ᵥ x) - x ⬝ᵥ (B *ᵥ x)| ≤
      ε * Fintype.card ι * (∑ i, x i ^ 2) := by
  have he : x ⬝ᵥ (A *ᵥ x) - x ⬝ᵥ (B *ᵥ x) =
      ∑ i, ∑ j, x i * (A i j - B i j) * x j := by
    simp only [dotProduct, mulVec, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  have hs : (∑ i, |x i|) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, x i ^ 2 := by
    simpa only [Finset.card_univ, sq_abs] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i ↦ |x i|))
  calc
    _ ≤ ∑ i, |∑ j, x i * (A i j - B i j) * x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |x i| * ε * |x j| := by
      apply Finset.sum_le_sum
      intro i _
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      apply Finset.sum_le_sum
      intro j _
      simp only [abs_mul]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hAB i j) (abs_nonneg _)) (abs_nonneg _)
    _ = ε * (∑ i, |x i|) ^ 2 := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
      ring
    _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs hε

/-- A small entrywise covariance perturbation preserves half a uniform lower quadratic bound. -/
theorem entrywise_covariance_lower {ι : Type*} [Fintype ι]
    (A B : Matrix ι ι ℝ) (c ε : ℝ) (hε : 0 ≤ ε)
    (hAB : ∀ i j, |A i j - B i j| ≤ ε)
    (hB : ∀ x : ι → ℝ, c * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (B *ᵥ x))
    (hsmall : ε * Fintype.card ι ≤ c / 2) (x : ι → ℝ) :
    (c / 2) * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (A *ᵥ x) := by
  have hh := entrywise_quadratic_error A B ε hε hAB x
  have he := (abs_le.mp hh).1
  have hs := mul_le_mul_of_nonneg_right hsmall
    (show 0 ≤ ∑ i, x i ^ 2 from Finset.sum_nonneg (fun i _ ↦ sq_nonneg (x i)))
  linarith [hB x]

/-- Hermitian entrywise perturbations retain positive definiteness under the same bound. -/
theorem entrywise_covariance_posDef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (hA : A.IsHermitian) (c ε : ℝ) (hc : 0 < c) (hε : 0 ≤ ε)
    (hAB : ∀ i j, |A i j - B i j| ≤ ε)
    (hB : ∀ x : ι → ℝ, c * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (B *ᵥ x))
    (hsmall : ε * Fintype.card ι ≤ c / 2) : A.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hA
  intro x hx
  have hex : ∃ i, x i ≠ 0 := by
    by_contra! hh
    exact hx (funext hh)
  obtain ⟨i, hi⟩ := hex
  have hs : 0 < ∑ j, x j ^ 2 :=
    (Finset.sum_pos_iff_of_nonneg (fun j _ ↦ sq_nonneg (x j))).mpr
      ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩
  have hh := (mul_pos (div_pos hc (by norm_num)) hs).trans_le
    (entrywise_covariance_lower A B c ε hε hAB hB hsmall x)
  simpa only [star_trivial] using hh

end SRWTightness
