import SRWTightness.SuffixSumEnergy
import Mathlib.LinearAlgebra.Matrix.PosDef

open Matrix

namespace SRWTightness

noncomputable def incrementCovariance {n : ℕ} (d : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  .of fun i j ↦ ∑ k, if k ≤ i ∧ k ≤ j then d k else 0

noncomputable def incrementTime {n : ℕ} (d : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ k, if k ≤ i then d k else 0

theorem incrementTime_mono {n : ℕ} (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i) : Monotone (incrementTime d) := by
  intro i j hij
  apply Finset.sum_le_sum
  intro k _
  by_cases hki : k ≤ i
  · simp only [hki, hki.trans hij, ↓reduceIte, le_refl]
  · by_cases hkj : k ≤ j
    · simpa only [hki, hkj, ↓reduceIte] using hd k
    · simp [hki, hkj]

theorem incrementCovariance_eq_min {n : ℕ} (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i) (i j : Fin n) :
    incrementCovariance d i j = min (incrementTime d i) (incrementTime d j) := by
  have he (i j : Fin n) (hij : i ≤ j) : incrementCovariance d i j = incrementTime d i := by
    simp only [incrementCovariance, Matrix.of_apply, incrementTime]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k ≤ i
    · simp [hk, hk.trans hij]
    · simp [hk]
  by_cases hij : i ≤ j
  · rw [he i j hij, min_eq_left (incrementTime_mono d hd hij)]
  · have hji : j ≤ i := le_of_not_ge hij
    have hs : incrementCovariance d i j = incrementCovariance d j i := by
      simp only [incrementCovariance, Matrix.of_apply, and_comm]
    rw [hs, he j i hji, min_eq_right (incrementTime_mono d hd hji)]

theorem incrementCovariance_quadratic {n : ℕ} (d x : Fin n → ℝ) :
    (∑ i, ∑ j, x i * incrementCovariance d i j * x j) =
      ∑ k, d k * suffixSum x k.val ^ 2 := by
  have ht (i j k : Fin n) : x i * (if k ≤ i ∧ k ≤ j then d k else 0) * x j =
      d k * (if k.val ≤ i.val then x i else 0) * (if k.val ≤ j.val then x j else 0) := by
    by_cases hi : k ≤ i <;> by_cases hj : k ≤ j <;> simp_all only [Fin.le_def, ↓reduceIte, and_self,
      and_false, false_and, true_and, mul_zero, zero_mul]
    <;> ring
  calc
    _ = ∑ i, ∑ j, ∑ k, x i * (if k ≤ i ∧ k ≤ j then d k else 0) * x j := by
      simp only [incrementCovariance, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
    _ = ∑ i, ∑ k, ∑ j, x i * (if k ≤ i ∧ k ≤ j then d k else 0) * x j := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, x i * (if k ≤ i ∧ k ≤ j then d k else 0) * x j := Finset.sum_comm
    _ = _ := by
      simp_rw [ht]
      apply Finset.sum_congr rfl
      intro k _
      simp only [suffixSum, pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- Uniform lower bound with no dependence on the number of observation times. -/
theorem incrementCovariance_quadratic_lower {n : ℕ} (d x : Fin n → ℝ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hd : ∀ i, δ ≤ d i) :
    (δ / 4) * (∑ i, x i ^ 2) ≤ ∑ i, ∑ j, x i * incrementCovariance d i j * x j := by
  have hh : δ * (∑ k : Fin n, suffixSum x k.val ^ 2) ≤ ∑ k, d k * suffixSum x k.val ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun k _ ↦ mul_le_mul_of_nonneg_right (hd k) (sq_nonneg _))
  rw [incrementCovariance_quadratic]
  have hm := mul_le_mul_of_nonneg_left (square_sum_le_four_suffix_energy x) hδ
  nlinarith

theorem incrementCovariance_posDef {n : ℕ} (d : Fin n → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (hd : ∀ i, δ ≤ d i) : (incrementCovariance d).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · apply Matrix.IsHermitian.ext
    intro i j
    simp only [star_trivial, incrementCovariance, Matrix.of_apply, and_comm]
  · intro x hx
    have hex : ∃ i, x i ≠ 0 := by
      by_contra! hh
      exact hx (funext hh)
    obtain ⟨i, hi⟩ := hex
    have hs : 0 < ∑ i, x i ^ 2 :=
      (Finset.sum_pos_iff_of_nonneg (fun j _ ↦ sq_nonneg (x j))).mpr ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero hi⟩
    have hh := (mul_pos (div_pos hδ (by norm_num)) hs).trans_le
      (incrementCovariance_quadratic_lower d x δ hδ.le hd)
    simpa only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, Finset.mul_sum, mul_assoc] using hh

end SRWTightness
